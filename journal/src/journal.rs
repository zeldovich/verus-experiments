use std::collections::VecDeque;
use std::sync::Arc;

use vstd::prelude::*;
// use vstd::bytes::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use vstd::logatom::*;
use vstd::tokens::frac::*;

use sl::seq_view::*;
// use sl::seq_prefix::*;

use super::pmem::*;
use super::codec::*;
// use super::pmem_util::*;

verus! {
    // GWrite is the spec-level representation of a single Write.
    pub struct GWrite {
        pub addr: usize,
        pub data: Seq<u8>,
    }

    pub struct CrashInvState {
        // Client view of pmem's durable resource.
        durable: GhostVar<Seq<u8>>,

        // Authoritative view of committed state.
        committed: SeqAuth<u8>,

        // Committed writes that have not been installed yet.
        // Currently there's just one transaction that could be in progress,
        // but could eventually pipeline this.
        pending: GhostVarAuth<Seq<GWrite>>,
    }

    pub struct CrashInvPred {
        durable_id: int,
        committed_id: int,
        pending_id: int,
    }

    pub open spec fn apply_write(state: Seq<u8>, write: GWrite) -> Seq<u8> {
        state.update_range(write.addr as int, write.data)
    }

    pub open spec fn apply_writes(state: Seq<u8>, writes: Seq<GWrite>) -> Seq<u8> {
        writes.fold_left(state, |s, w: GWrite| apply_write(s, w))
    }

    spec fn seq_equal_except_range<A>(s0: Seq<A>, s1: Seq<A>, off: int, len: int) -> bool
        recommends
            0 <= off,
            0 <= len,
            off + len <= s0.len(),
            s0.len() == s1.len(),
    {
        &&& s0.len() == s1.len()
        &&& forall |i| 0 <= i < s0.len() ==> {
            ||| off <= i < off + len
            ||| s0[i] == s1[i]
        }
    }

    proof fn apply_writes_range_equal(state0: Seq<u8>, state1: Seq<u8>, writes: Seq<GWrite>, addr: int, len: int)
        requires
            seq_equal_except_range(state0, state1, addr, len)
        ensures
            seq_equal_except_range(apply_writes(state0, writes), apply_writes(state1, writes), addr, len)
        decreases
            writes.len()
    {
        if writes.len() > 0 {
            apply_writes_range_equal(state0, state1, writes.take(writes.len()-1), addr, len);
        }
    }

    impl InvariantPredicate<CrashInvPred, CrashInvState> for CrashInvPred
    {
        closed spec fn inv(k: CrashInvPred, inner: CrashInvState) -> bool {
            &&& inner.durable.id() == k.durable_id
            &&& inner.committed.valid(k.committed_id)
            &&& inner.pending.id() == k.pending_id
            &&& inner.committed@ == apply_writes(inner.durable@, inner.pending@)
        }
    }

    pub struct JWrite<'a> {
        pub addr: usize,
        pub bytes: &'a [u8],
        pub read_frac: Tracked<SeqFrac<u8>>,
    }

    impl<'a> DeepView for JWrite<'a> {
        type V = GWrite;

        closed spec fn deep_view(&self) -> GWrite {
            GWrite{
                addr: self.addr,
                data: self.bytes.deep_view(),
            }
        }
    }

    impl Encoding for GWrite {
        closed spec fn encoding(self) -> Seq<u8> {
            self.addr.encoding() + self.data.encoding()
        }
    }

    impl<'a> Encodable for JWrite<'a> {
        exec fn encode(&self, buf: &mut Vec<u8>) {
            self.addr.encode(buf);
            self.bytes.encode(buf);
        }
    }

    struct JWriteVec {
        pub addr: usize,
        pub bytes: Vec<u8>,
    }

    impl DeepView for JWriteVec {
        type V = GWrite;

        closed spec fn deep_view(&self) -> GWrite {
            GWrite{
                addr: self.addr,
                data: self.bytes.deep_view(),
            }
        }
    }

    impl Encodable for JWriteVec {
        exec fn encode(&self, buf: &mut Vec<u8>) {
            self.addr.encode(buf);
            self.bytes.encode(buf);
        }
    }

    impl Decodable for JWriteVec {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            broadcast use is_prefix_of_trans;
            broadcast use is_prefix_of_skip;

            let addr = usize::decode(buf, Ghost(oldv.addr));
            let bytes = Vec::decode(buf, Ghost(oldv.bytes));

            Self{
                addr: addr,
                bytes: bytes,
            }
        }
    }

    struct InstallationWrite<'a> {
        credit: OpenInvariantCredit,
        inv: Arc<AtomicInvariant<CrashInvPred, CrashInvState, CrashInvPred>>,
        read: SeqFrac<u8>,
        prefix: &'a GhostVar<Seq<GWrite>>,
        prefixpos: usize,
    }

    proof fn installation_write_idempotent(durable: Seq<u8>, pending: Seq<GWrite>, addr: int, data: Seq<u8>, pos: int)
        requires
            pending[pos].addr == addr,
            pending[pos].data.len() == data.len(),
            0 <= pos < pending.len(),
        ensures
            apply_writes(durable, pending) == apply_writes(durable.update_range(addr, data), pending)
    {
        let durableU = durable.update_range(addr, data);
        let pending0 = pending.take(pos);
        let dpos  = apply_writes(durable,  pending0);
        let dposU = apply_writes(durableU, pending0);
        apply_writes_range_equal(durable, durableU, pending0, addr, data.len() as int);

        let w = pending[pos];
        assert(apply_write(dpos, w) == apply_write(dposU, w));

        let pending1 = pending.skip(pos);

        reveal_with_fuel(Seq::fold_left, 2);
        assert(apply_writes(dpos,  pending1.take(1)) == apply_write(dpos,  w));
        assert(apply_writes(dposU, pending1.take(1)) == apply_write(dposU, w));
    }

    impl<'a> MutLinearizer<Write> for InstallationWrite<'a> {
        type Completion = SeqFrac<u8>;

        closed spec fn namespaces(self) -> Set<int> {
            set![self.inv.namespace()]
        }

        closed spec fn pre(self, op: Write) -> bool {
            &&& self.read.valid(op.read_id)
            &&& self.inv.constant().durable_id == op.durable_id

            &&& op.data.len() > 0
            &&& self.read.off() == op.addr
            &&& self.read@.len() == op.data.len()

            &&& self.prefix.id() == self.inv.constant().pending_id
            &&& self.prefix@[self.prefixpos as int].addr == op.addr
            &&& self.prefix@[self.prefixpos as int].data == op.data
            &&& self.prefixpos < self.prefix@.len()
        }

        closed spec fn post(self, op: Write, e: <Write as MutOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r.valid(op.read_id)
            &&& r.off() == self.read.off()
            &&& r@ == op.data
        }

        proof fn apply(tracked self, op: Write, tracked r: &mut <Write as MutOperation>::Resource, new_state: <Write as MutOperation>::NewState, e: &<Write as MutOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;
            mself.read.agree(&r.read);
            mself.read.update(&mut r.read, op.data);

            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                inner.pending.agree(mself.prefix);
                installation_write_idempotent(r.durable@, inner.pending@, op.addr as int, new_state, mself.prefixpos as int);
                r.durable.update(&mut inner.durable, r.durable@.update_range(op.addr as int, new_state));
            });

            assert(op.ensures(*old(r), *r, new_state));
            mself.read
        }

        proof fn peek(tracked &self, op: Write, tracked r: &<Write as MutOperation>::Resource) {
            self.read.agree(&r.read);
        }
    }

    struct InstallationFlush<'a> {
        credit: OpenInvariantCredit,
        inv: Arc<AtomicInvariant<CrashInvPred, CrashInvState, CrashInvPred>>,
        prefix: GhostVar<Seq<GWrite>>,
        readfracs: &'a Seq<SeqFrac<u8>>,
    }

    proof fn installed_durable_after_flush(
        tracked durable: &GhostVar<Seq<u8>>,
        tracked read: &SeqAuth<u8>,
        tracked pending: &GhostVarAuth<Seq<GWrite>>,
        tracked readfracs: &Seq<SeqFrac<u8>>,
        n: int
    )
        requires
            0 <= n <= readfracs.len(),
            readfracs.len() <= pending@.len(),
            durable@ == read@,
            read.inv(),
            forall |i| 0 <= i < readfracs.len() ==> {
                &&& (#[trigger] readfracs[i]).valid(read.id())
                &&& readfracs[i].off() == pending@[i].addr
                &&& readfracs[i]@ == pending@[i].data
            },
        ensures
            durable@ == apply_writes(durable@, pending@.take(n)),
        decreases
            n
    {
        if n > 0 {
            installed_durable_after_flush(durable, read, pending, readfracs, n-1);

            // Set up for lemma_fold_left_split().
            assert(pending@.subrange(0, n-1) == pending@.subrange(0, n).subrange(0, n-1));
            assert(pending@.subrange(n-1, n) == pending@.subrange(0, n).subrange(n-1, n));

            readfracs.tracked_borrow(n-1).agree(read);
            assert(durable@ == apply_write(durable@, pending@[n-1]));
        }
    }

    impl<'a> ReadLinearizer<Flush> for InstallationFlush<'a> {
        type Completion = GhostVar<Seq<GWrite>>;

        closed spec fn namespaces(self) -> Set<int> {
            set![self.inv.namespace()]
        }

        closed spec fn pre(self, op: Flush) -> bool {
            &&& self.prefix.id() == self.inv.constant().pending_id
            &&& self.readfracs.len() == self.prefix@.len()
            &&& self.inv.constant().durable_id == op.durable_id
            &&& forall |i| 0 <= i < self.readfracs.len() ==> {
                &&& (#[trigger] self.readfracs[i]).valid(op.read_id)
                &&& self.readfracs[i].off() == self.prefix@[i].addr
                &&& self.readfracs[i]@ == self.prefix@[i].data
            }
        }

        closed spec fn post(self, op: Flush, e: <Write as MutOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r.id() == self.inv.constant().pending_id
            &&& r@.len() == 0
        }

        proof fn apply(tracked self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource, e: &<Flush as ReadOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                inner.pending.agree(&mself.prefix);
                r.durable.agree(&inner.durable);

                installed_durable_after_flush(&inner.durable, &r.read, &inner.pending, mself.readfracs, mself.readfracs.len() as int);

                inner.pending.update(&mut mself.prefix, Seq::empty());
            });

            mself.prefix
        }

        proof fn peek(tracked &self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource) {
        }
    }

    struct InstallerState {
        prefix: Tracked<GhostVar<Seq<GWrite>>>,
    }

    struct InstallerPred {
        pending_id: int,
    }

    impl RwLockPredicate<InstallerState> for InstallerPred {
        closed spec fn inv(self, s: InstallerState) -> bool {
            &&& s.prefix@.id() == self.pending_id

            // XXX for now, no concurrency for installation; one transaction at a time
            &&& s.prefix@@.len() == 0
        }
    }

    pub struct Journal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        pmem: Arc<PM>,
        inv: Arc<AtomicInvariant<CrashInvPred, CrashInvState, CrashInvPred>>,
        installer: RwLock<InstallerState, InstallerPred>,
    }

    impl<PM> Journal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        pub closed spec fn read_id(self) -> int {
            self.pmem.read_id()
        }

        pub closed spec fn durable_id(self) -> int {
            self.pmem.durable_id()
        }

        pub closed spec fn committed_id(self) -> int {
            self.inv.constant().committed_id
        }

        pub closed spec fn inv(self) -> bool {
            &&& self.inv.constant().durable_id == self.pmem.durable_id()
            &&& self.inv.constant().pending_id == self.installer.pred().pending_id
        }

        spec fn pending_id(self) -> int {
            self.inv.constant().pending_id
        }

        pub closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

        exec fn install<'a>(&self, mut writes: VecDeque<JWrite<'a>>, Tracked(prefix): Tracked<GhostVar<Seq<GWrite>>>) -> (result: (Tracked<Seq<SeqFrac<u8>>>, Tracked<GhostVar<Seq<GWrite>>>))
            requires
                self.inv(),
                writes@.len() == prefix@.len(),
                prefix.id() == self.pending_id(),
                forall |i| 0 <= i < writes@.len() ==> {
                    &&& (#[trigger] writes@[i]).addr == prefix@[i].addr
                    &&& writes@[i].bytes@ == prefix@[i].data
                    &&& writes@[i].bytes@.len() > 0
                    &&& writes@[i].read_frac@.valid(self.read_id())
                    &&& writes@[i].read_frac@.off() == writes@[i].addr
                    &&& writes@[i].read_frac@@.len() == writes@[i].bytes@.len()
                },
            ensures
                result.0@.len() == writes@.len(),
                result.1@.id() == self.pending_id(),
                result.1@@.len() == 0,
                forall |i| 0 <= i < result.0@.len() ==> {
                    &&& (#[trigger] result.0@[i]).valid(self.read_id())
                    &&& result.0@[i].off() == writes@[i].read_frac@.off()
                    &&& result.0@[i]@ == writes@[i].bytes@
                },
        {
            broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
            let nwrites = writes.len();
            let mut old_writes = writes;
            let tracked mut new_read_fracs = Seq::<SeqFrac<u8>>::tracked_empty();
            for i in 0..nwrites
                invariant
                    writes@.len() == nwrites,
                    old_writes@ =~= writes@.skip(i as int),
                    i == new_read_fracs.len(),
                    forall |j| 0 <= j < i ==> {
                        &&& (#[trigger] new_read_fracs[j]).valid(self.read_id())
                        &&& new_read_fracs[j].off() == writes@[j].read_frac@.off()
                        &&& new_read_fracs[j]@ == writes@[j].bytes@
                    },
                    forall |j| 0 <= j < writes@.len() ==> {
                        &&& (#[trigger] writes@[j]).addr == prefix@[j].addr
                        &&& writes@[j].bytes@ == prefix@[j].data
                        &&& writes@[j].bytes@.len() > 0
                        &&& writes@[j].read_frac@.valid(self.read_id())
                        &&& writes@[j].read_frac@.off() == writes@[j].addr
                        &&& writes@[j].read_frac@@.len() == writes@[j].bytes@.len()
                    },
                    self.pmem.durable_id() == self.inv.constant().durable_id,
                    prefix.id() == self.inv.constant().pending_id,
                    nwrites <= prefix@.len(),
            {
                let w = old_writes.pop_front().unwrap();
                let credit = create_open_invariant_credit();
                let tracked iw = InstallationWrite{
                    credit: credit.get(),
                    inv: self.inv.clone(),
                    read: w.read_frac.get(),
                    prefix: &prefix,
                    prefixpos: i,
                };
                let r = self.pmem.write::<InstallationWrite>(w.addr, w.bytes, Tracked(iw));
                proof {
                    new_read_fracs.tracked_push(r.get());
                }
            }

            let credit = create_open_invariant_credit();
            let tracked ifl = InstallationFlush{
                credit: credit.get(),
                inv: self.inv.clone(),
                prefix: prefix,
                readfracs: &new_read_fracs,
            };

            let prefix = self.pmem.flush::<InstallationFlush>(Tracked(ifl));

            (Tracked(new_read_fracs), prefix)
        }

        exec fn log<Lin, 'a>(&self, mut writes: VecDeque<JWrite<'a>>, Tracked(lin): Tracked<Lin>) -> (result: (Tracked<Seq<SeqFrac<u8>>>, Tracked<Lin::Completion>))
            where
                Lin: MutLinearizer<Commit>,
            requires
                self.inv(),
                forall |i| 0 <= i < writes@.len() ==> {
                    &&& (#[trigger] writes@[i]).bytes@.len() > 0
                    &&& writes@[i].read_frac@.valid(self.read_id())
                    &&& writes@[i].read_frac@.off() == writes@[i].addr
                    &&& writes@[i].read_frac@@.len() == writes@[i].bytes@.len()
                },
                lin.pre(Commit{ committed_id: self.committed_id(), writes: writes.deep_view() }),
                !lin.namespaces().contains(self.namespace()),
            ensures
                result.0@.len() == writes@.len(),
                forall |i| 0 <= i < result.0@.len() ==> {
                    &&& (#[trigger] result.0@[i]).valid(self.read_id())
                    &&& result.0@[i].off() == writes@[i].read_frac@.off()
                    &&& result.0@[i]@ == writes@[i].bytes@
                },
                lin.post(Commit{ committed_id: self.committed_id(), writes: writes.deep_view() }, true, result.1@),
        {
            let ghost gwrites = writes.deep_view();
            let ghost op = Commit{
                committed_id: self.committed_id(),
                writes: gwrites,
            };

            let (installer, handle) = self.installer.acquire_write();
            let tracked mut prefix = installer.prefix.get();
            let tracked mut complete;
            open_atomic_invariant!(&self.inv => inner => {
                proof {
                    complete = lin.apply(op, &mut inner.committed, true, &true);

                    let pending0 = inner.pending@;

                    inner.pending.update(&mut prefix, gwrites);

                    // Set up for lemma_fold_left_split().
                    assert(inner.pending@.take(pending0.len() as int) == pending0);
                    assert(inner.pending@.skip(pending0.len() as int) == gwrites);

                    assert(CrashInvPred::inv(self.inv.constant(), inner));
                }
            });

            assert(forall |i: int| 0 <= i < writes@.len() ==> gwrites[i].data == (#[trigger] writes@[i]).bytes@);

            let (Tracked(res), Tracked(prefix)) = self.install(writes, Tracked(prefix));
            let installer = InstallerState{
                prefix: Tracked(prefix),
            };

            handle.release_write(installer);

            (Tracked(res), Tracked(complete))
        }
    }

    pub struct Commit {
        pub committed_id: int,
        pub writes: Seq<GWrite>,
    }

    impl MutOperation for Commit {
        type Resource = SeqAuth<u8>;
        type ExecResult = bool;
        type NewState = bool;

        open spec fn requires(self, r: Self::Resource, new_state: Self::NewState, e: Self::ExecResult) -> bool {
            &&& r.valid(self.committed_id)
            &&& e == new_state
        }

        open spec fn ensures(self, r: Self::Resource, new_r: Self::Resource, new_state: Self::NewState) -> bool {
            if new_state {
                &&& new_r.valid(self.committed_id)
                &&& new_r@ == apply_writes(r@, self.writes)
            } else {
                &&& new_r == r
            }
        }
    }
}
