use std::collections::VecDeque;
use std::sync::Arc;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::rwlock::*;
use vstd::invariant::*;
use vstd::logatom::*;
use vstd::tokens::frac::*;

use sl::seq_view::*;
use sl::seq_prefix::*;

use super::pmem::*;
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
        pending: SeqPrefixAuth<GWrite>,
    }

    pub struct CrashInvPred {
        durable_id: int,
        committed_id: int,
        pending_id: int,
    }

    spec fn apply_write(state: Seq<u8>, write: GWrite) -> Seq<u8> {
        state.update_range(write.addr as int, write.data)
    }

    spec fn apply_writes(state: Seq<u8>, writes: Seq<GWrite>) -> Seq<u8> {
        writes.fold_left(state, |s, w: GWrite| apply_write(s, w))
    }

    impl InvariantPredicate<CrashInvPred, CrashInvState> for CrashInvPred
    {
        closed spec fn inv(k: CrashInvPred, inner: CrashInvState) -> bool {
            &&& inner.durable.id() == k.durable_id
            &&& inner.committed.valid(k.committed_id)
            &&& inner.pending.valid(k.pending_id)
            &&& inner.committed@ == apply_writes(inner.durable@, inner.pending@)
        }
    }

    pub struct JWrite<'a> {
        pub addr: usize,
        pub bytes: &'a [u8],
        pub read_frac: Tracked<SeqFrac<u8>>,
    }

    struct InstallationWrite {
        credit: OpenInvariantCredit,
        inv: Arc<AtomicInvariant<CrashInvPred, CrashInvState, CrashInvPred>>,
        read: SeqFrac<u8>,
    }

    impl MutLinearizer<Write> for InstallationWrite {
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
                r.durable.update(&mut inner.durable, r.durable@.update_range(op.addr as int, new_state));
                assert(CrashInvPred::inv(mself.inv.constant(), inner));
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
        prefix: SeqPrefix<GWrite>,
        readfracs: &'a Seq<SeqFrac<u8>>,
    }

    proof fn installed_durable_after_flush(
        tracked durable: &GhostVar<Seq<u8>>,
        tracked read: &SeqAuth<u8>,
        tracked pending: &SeqPrefixAuth<GWrite>,
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
            durable@ == apply_writes(durable@, pending@.subrange(0, n)),
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
        type Completion = SeqPrefix<GWrite>;

        closed spec fn namespaces(self) -> Set<int> {
            set![self.inv.namespace()]
        }

        closed spec fn pre(self, op: Flush) -> bool {
            &&& self.prefix.valid(self.inv.constant().pending_id)
            &&& self.readfracs.len() <= self.prefix@.len()
            &&& self.inv.constant().durable_id == op.durable_id
            &&& forall |i| 0 <= i < self.readfracs.len() ==> {
                &&& (#[trigger] self.readfracs[i]).valid(op.read_id)
                &&& self.readfracs[i].off() == self.prefix@[i].addr
                &&& self.readfracs[i]@ == self.prefix@[i].data
            }
        }

        closed spec fn post(self, op: Flush, e: <Write as MutOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r.valid(self.inv.constant().pending_id)
            &&& r@ == self.prefix@.subrange(self.readfracs.len() as int, self.prefix@.len() as int)
        }

        proof fn apply(tracked self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource, e: &<Flush as ReadOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                inner.pending.agree(&mself.prefix);
                r.durable.agree(&inner.durable);

                installed_durable_after_flush(&inner.durable, &r.read, &inner.pending, mself.readfracs, mself.readfracs.len() as int);

                inner.pending.truncate(&mut mself.prefix, mself.readfracs.len() as int);
            });

            mself.prefix
        }

        proof fn peek(tracked &self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource) {
        }
    }

    pub struct Journal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        pmem: Arc<PM>,
        inv: Arc<AtomicInvariant<CrashInvPred, CrashInvState, CrashInvPred>>,
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
        }

        spec fn pending_id(self) -> int {
            self.inv.constant().pending_id
        }

        pub closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

        exec fn install<'a>(&self, mut writes: VecDeque<JWrite<'a>>, Tracked(prefix): Tracked<SeqPrefix<GWrite>>) -> (result: (Tracked<Seq<SeqFrac<u8>>>, Tracked<SeqPrefix<GWrite>>))
            requires
                self.inv(),
                writes@.len() <= prefix@.len(),
                prefix.valid(self.pending_id()),
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
                result.1@.valid(self.pending_id()),
                result.1@@ == prefix@.subrange(writes@.len() as int, prefix@.len() as int),
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
                    old_writes@ =~= writes@.subrange(i as int, writes@.len() as int),
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
            {
                let w = old_writes.pop_front().unwrap();
                let credit = create_open_invariant_credit();
                let tracked iw = InstallationWrite{
                    credit: credit.get(),
                    inv: self.inv.clone(),
                    read: w.read_frac.get(),
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
    }

/*
    pub struct LockedJournal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        pmem: Arc<PM>,
        addr: usize,
        len: usize,
        fracs: Tracked<Fracs>,
    }

    pub struct Write<'a> {
        pub addr: usize,
        pub bytes: &'a [u8],
        pub read_frac: Tracked<SeqFrac<u8>>,
    }

    impl<PM> LockedJournal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        spec fn inv(self) -> bool {
            &&& self.fracs@.read.valid(self.pmem.read_id())
            &&& self.fracs@.durable.valid(self.pmem.durable_id())
            &&& self.fracs@.read.off() == self.addr
            &&& self.fracs@.durable.off() == self.addr
            &&& self.fracs@.read@.len() == self.len
            &&& self.fracs@.durable@.len() == self.len
            &&& self.len >= 8
        }

        fn record(self, mut writeset: VecDeque<Write>)
            requires
                self.inv(),
        {
            let nwrites = writeset.len();

/*
            let next_addr = self.addr + 8;
            for i in 0..nwrites {
                let w = writeset.pop_front().unwrap();
                self.pmem.write(next_addr, u64_to_le_bytes(w.addr as u64).as_slice(), self.fracs);
                self.pmem.write(next_addr+8, u64_to_le_bytes(w.bytes.len() as u64).as_slice(), self.fracs);
                self.pmem.write(next_addr+16, w.bytes, self.fracs);
            }
            */

            self.pmem.write(self.addr, u64_to_le_bytes(nwrites as u64).as_slice(), self.fracs);
        }
    }

    pub struct Pred {
    }

    impl<PM> RwLockPredicate<LockedJournal<PM>> for Pred
        where
            PM: PersistentMemoryRegion,
    {
        closed spec fn inv(self, j: LockedJournal<PM>) -> bool {
            &&& j.inv()
        }
    }

    pub struct Commit<'a> {
        pub committed_id: int,
        pub writes: Seq<Write<'a>>,
    }

    impl<'a> MutOperation for Commit<'a> {
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
            } else {
                &&& new_r == r
            }
        }
    }

    impl<PM> Journal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        fn install<'a, Lin>(&self, writes: &mut Vec<Write>)
            where
                Lin: MutLinearizer<Commit<'a>>
        {
            let nwrites = writes.len();
            for i in 0..nwrites
                invariant
                    nwrites == writes.len(),
            {
                let w = &writes[i];
                // self.pmem.write(w.addr, w.bytes, Tracked());
            }
        }

        pub fn commit<'a, Lin>(&self, writes: &mut Vec<Write>, Tracked(lin): Tracked<Lin>) -> (result: (bool, Tracked<Lin::Completion>))
            where
                Lin: MutLinearizer<Commit<'a>>
            requires
                lin.pre(Commit{ committed_id: self.committed_id(), writes: old(writes)@ }),
                !lin.namespaces().contains(self.namespace()),
            ensures
                lin.post(Commit{ committed_id: self.committed_id(), writes: old(writes)@ }, result.0, result.1@),
        {
            let ghost op = Commit{ committed_id: self.committed_id(), writes: writes@ };
            let commit = false;
            let tracked complete;
            open_atomic_invariant!(&self.inv => inner => {
                proof {
                    complete = lin.apply(op, &mut inner.committed, commit, &commit);
                }
            });
            (commit, Tracked(complete))
        }
    }
    */
}
