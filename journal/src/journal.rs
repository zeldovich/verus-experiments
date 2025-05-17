use std::collections::VecDeque;
use std::sync::Arc;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use vstd::logatom::*;

use sl::seq_view::*;
use sl::seq_helper::*;

use super::pmem::*;
use super::pmem_util::*;

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
        pending: Seq<GWrite>,
    }

    pub struct CrashInvPred {
        durable_id: int,
        committed_id: int,
    }

    spec fn apply_writes(state: Seq<u8>, writes: Seq<GWrite>) -> Seq<u8> {
        writes.fold_right(|w: GWrite, s| update_seq(s, w.addr as int, w.data), state)
    }

    impl InvariantPredicate<CrashInvPred, CrashInvState> for CrashInvPred
    {
        closed spec fn inv(k: CrashInvPred, inner: CrashInvState) -> bool {
            &&& inner.durable.valid(k.durable_id)
            &&& inner.committed.valid(k.committed_id)
            &&& inner.committed@ == apply_writes(inner.durable@, inner.pending)
        }
    }

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

    pub struct Journal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        pmem: Arc<PM>,
        lk: RwLock<LockedJournal<PM>, Pred>,
        inv: AtomicInvariant<CrashInvPred, CrashInvState, CrashInvPred>,
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
        pub closed spec fn committed_id(self) -> int {
            self.inv.constant().committed_id
        }

        pub closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

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
}
