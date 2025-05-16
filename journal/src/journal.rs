use std::collections::VecDeque;
use std::sync::Arc;

use vstd::prelude::*;
use vstd::bytes::*;
use vstd::rwlock::*;
use vstd::invariant::*;
use vstd::logatom::*;

use sl::seq_view::*;

use super::pmem::*;
use super::pmem_util::*;

verus! {
    pub struct CrashInvState {
        // client view of pmem's durable resource
        durable: SeqFrac<u8>,

        // authoritative view of journal's resource
        committed: SeqAuth<u8>,
    }

    pub struct CrashInvPred {
        durable_id: int,
        committed_id: int,
    }

    impl InvariantPredicate<CrashInvPred, CrashInvState> for CrashInvPred
    {
        closed spec fn inv(k: CrashInvPred, inner: CrashInvState) -> bool {
            &&& inner.durable.valid(k.durable_id)
            &&& inner.committed.valid(k.committed_id)

            // XXX For now, no outstanding transactions...
            &&& inner.committed@ == inner.durable@
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
            &&& e == new_state
        }

        open spec fn ensures(self, r: Self::Resource, new_r: Self::Resource, new_state: Self::NewState) -> bool {
            &&& true
        }
    }

    impl<PM> Journal<PM>
        where
            PM: PersistentMemoryRegion,
    {
        pub closed spec fn committed_id(self) -> int {
            self.inv.constant().committed_id
        }

        pub fn commit<'a, Lin>(&self, writes: VecDeque<Write>, Tracked(lin): Tracked<Lin>) -> (result: (bool, Tracked<Lin::Completion>))
            where
                Lin: MutLinearizer<Commit<'a>>
            requires
                lin.pre(Commit{ committed_id: self.committed_id(), writes: writes@ }),
            ensures
                lin.post(Commit{ committed_id: self.committed_id(), writes: writes@ }, result.0, result.1@),
        {
            (false, 0)
        }
    }
}
