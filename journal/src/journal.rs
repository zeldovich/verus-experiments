use std::collections::VecDeque;
use std::sync::Arc;

use vstd::prelude::*;
// use vstd::bytes::*;
// use vstd::rwlock::*;
use vstd::invariant::*;
use vstd::logatom::*;

use sl::seq_view::*;
use sl::seq_helper::*;
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
        durable: SeqFrac<u8>,

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

    spec fn apply_writes(state: Seq<u8>, writes: Seq<GWrite>) -> Seq<u8> {
        writes.fold_right(|w: GWrite, s| update_seq(s, w.addr as int, w.data), state)
    }

    impl InvariantPredicate<CrashInvPred, CrashInvState> for CrashInvPred
    {
        closed spec fn inv(k: CrashInvPred, inner: CrashInvState) -> bool {
            &&& inner.durable.valid(k.durable_id)
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

        closed spec fn pre(self, op: Write) -> bool {
            &&& self.read.valid(op.read_id)
            &&& self.inv.constant().durable_id == op.durable_id

            &&& op.data.len() > 0
            &&& self.read.off() <= op.addr
            &&& op.addr + op.data.len() <= self.read.off() + self.read@.len()
        }

        closed spec fn post(self, op: Write, e: <Write as MutOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r.valid(op.read_id)
            &&& r.off() == self.read.off()
            &&& r@ == update_seq(self.read@, op.addr as int - self.read.off(), op.data)
        }

        proof fn apply(tracked self, op: Write, tracked r: &mut <Write as MutOperation>::Resource, new_state: <Write as MutOperation>::NewState, e: &<Write as MutOperation>::ExecResult) -> tracked Self::Completion {
            admit();
            self.read
        }

        proof fn peek(tracked &self, op: Write, tracked r: &<Write as MutOperation>::Resource) {
            self.read.agree(&r.read);
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

        exec fn install<'a>(&self, mut writes: VecDeque<JWrite<'a>>, Tracked(prefix): Tracked<&mut SeqPrefix<GWrite>>) -> (new_writes: VecDeque<JWrite<'a>>)
            requires
                writes@.len() <= old(prefix)@.len(),
                old(prefix).valid(self.pending_id()),
                forall |i| 0 <= i < writes@.len() ==> {
                    &&& (#[trigger] writes@[i]).addr == old(prefix)@[i].addr
                    &&& writes@[i].bytes@ == old(prefix)@[i].data
                    &&& writes@[i].bytes@.len() > 0
                    &&& writes@[i].read_frac@.valid(self.read_id())
                    &&& writes@[i].read_frac@.off() <= writes@[i].addr
                    &&& writes@[i].addr - writes@[i].read_frac@.off() + writes@[i].bytes@.len() <= writes@[i].read_frac@@.len()
                },
            ensures
                new_writes@.len() == writes@.len(),
                prefix.valid(self.pending_id()),
                prefix@ == old(prefix)@.subrange(writes@.len() as int, old(prefix)@.len() as int),
                forall |i| 0 <= i < new_writes@.len() ==> {
                    &&& (#[trigger] new_writes@[i]).addr == (#[trigger] writes@[i]).addr
                    &&& new_writes@[i].bytes == writes@[i].bytes
                    &&& new_writes@[i].read_frac@.valid(self.read_id())
                    &&& new_writes@[i].read_frac@.off() == writes@[i].read_frac@.off()
                    &&& new_writes@[i].read_frac@@ == update_seq(writes@[i].read_frac@@, writes@[i].addr - writes@[i].read_frac@.off(), writes@[i].bytes@)
                },
        {
            broadcast use vstd::std_specs::vecdeque::group_vec_dequeue_axioms;
            let nwrites = writes.len();
            let mut new_writes = VecDeque::new();
            for i in 0..nwrites
                invariant
                    i + writes@.len() == nwrites,
                    i == new_writes@.len(),
            {
                let w = writes.pop_front().unwrap();
                let credit = create_open_invariant_credit();
                let tracked iw = InstallationWrite{
                    credit: credit.get(),
                    inv: self.inv.clone(),
                    read: w.read_frac.get(),
                };
                let r = self.pmem.write::<InstallationWrite>(w.addr, w.bytes, Tracked(iw));
                new_writes.push_back(JWrite{
                    addr: w.addr,
                    bytes: w.bytes,
                    read_frac: r,
                });
            }

            open_atomic_invariant!(&self.inv => inner => {
                proof {
                    inner.pending.truncate(prefix, nwrites as int);
                    assume(CrashInvPred::inv(self.inv.constant(), inner));
                }
            });

            new_writes
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
