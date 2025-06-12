use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::logatom::*;

use sl::seq_view::*;

use super::pmem::*;

// This file provides a simple implementation of PersistentMemoryRegion,
// to ensure that the spec is implementable.  This implementation always
// persists data, stored in a Vec<u8>.

verus! {
    struct LockPred {
        read_id: int,
        durable_id: int,
    }

    struct LockedState {
        data: Vec<u8>,
        r: Tracked<PMResource>,
    }

    impl RwLockPredicate<LockedState> for LockPred {
        closed spec fn inv(self, v: LockedState) -> bool {
            &&& v.r@.read.valid(self.read_id)
            &&& v.r@.durable.valid(self.durable_id)
            &&& v.data@ == v.r@.read@
            &&& v.data@ == v.r@.durable@
            &&& v.r@.read.off() == 0
            &&& v.r@.durable.off() == 0
        }
    }

    pub struct SimpleMem {
        lk: RwLock<LockedState, LockPred>,
    }

    impl SimpleMem {
        pub exec fn new(sz: usize) -> (result: (SimpleMem, Tracked<SeqFrac<u8>>, Tracked<SeqFrac<u8>>))
            ensures
                result.1@.valid(result.0.read_id()),
                result.2@.valid(result.0.durable_id()),
                result.1@.off() == 0,
                result.2@.off() == 0,
                result.1@@.len() == sz,
                result.2@@ == result.1@@,
        {
            let mut data = Vec::new();
            data.resize(sz, 0);
            let tracked (read, read_frac) = SeqAuth::new(data@, 0);
            let tracked (durable, durable_frac) = SeqAuth::new(data@, 0);
            let locked = LockedState{
                data: data,
                r: Tracked(PMResource{
                    read: read,
                    durable: durable,
                }),
            };
            let ghost pred = LockPred{
                read_id: read.id(),
                durable_id: durable.id(),
            };
            let m = SimpleMem{
                lk: RwLock::new(locked, Ghost(pred)),
            };
            (m, Tracked(read_frac), Tracked(durable_frac))
        }
    }

    #[verifier::external_body]
    pub fn copy_from_slice(bytes: &[u8]) -> (out: Vec<u8>)
        ensures
            out@ == bytes@
    {
        let mut buffer = vec![0; bytes.len()];
        let mut buffer_slice = buffer.as_mut_slice();
        buffer_slice.copy_from_slice(bytes);
        buffer
    }

    impl PersistentMemoryRegion for SimpleMem {
        closed spec fn read_id(self) -> int {
            self.lk.pred().read_id
        }

        closed spec fn durable_id(self) -> int {
            self.lk.pred().durable_id
        }

        exec fn read<Lin>(&self, addr: usize, num_bytes: usize, Tracked(lin): Tracked<Lin>) -> (Vec<u8>, Tracked<Lin::Completion>)
            where
                Lin: ReadLinearizer<Read>,
        {
            let ghost op = Read{ read_id: self.read_id(), addr, num_bytes };
            let handle = self.lk.acquire_read();
            let state = handle.borrow();

            proof {
                lin.peek(op, &state.r.borrow().read);
            }

            let mut res = Vec::new();
            proof { vstd::std_specs::vec::axiom_spec_len(&state.data); }
            assert(res@ == state.data@.subrange(addr as int, addr as int));
            for i in 0..num_bytes
                invariant
                    addr + num_bytes <= state.data@.len(),
                    state.data@.len() <= usize::MAX,
                    res@ == state.data@.subrange(addr as int, addr + i as int),
            {
                res.push(state.data[addr+i]);
                assert(res@ == state.data@.subrange(addr as int, addr + i + 1 as int));
            }

            let tracked complete;
            proof {
                complete = lin.apply(op, &state.r.borrow().read, &res);
            }

            handle.release_read();

            (res, Tracked(complete))
        }

        exec fn write<Lin>(&self, addr: usize, bytes: &[u8], Tracked(lin): Tracked<Lin>) -> (Tracked<Lin::Completion>)
            where
                Lin: MutLinearizer<Write>,
        {
            let ghost op = Write{ read_id: self.read_id(), durable_id: self.durable_id(), addr, data: bytes@ };
            let (mut state, handle) = self.lk.acquire_write();

            proof {
                lin.peek(op, &state.r.borrow());
            }

            proof { vstd::std_specs::vec::axiom_spec_len(&state.data); }
            assert(state.data@ == state.r@.read@.update_subrange_with(addr as int, bytes@.subrange(0, 0)));
            for i in 0..bytes.len()
                invariant
                    addr + bytes@.len() <= state.data@.len(),
                    state.data@.len() <= usize::MAX,
                    state.data@ == state.r@.read@.update_subrange_with(addr as int, bytes@.subrange(0, i as int)),
                    state.r@.read.valid(op.read_id),
                    state.r@.durable.valid(op.durable_id),
                    state.r@.read@ == state.r@.durable@,
                    state.r@.read.off() == 0,
                    state.r@.durable.off() == 0,
            {
                state.data[addr+i] = bytes[i];
                assert(state.data@ == state.r@.read@.update_subrange_with(addr as int, bytes@.subrange(0, i+1 as int)));
            }

            let tracked complete;
            proof {
                complete = lin.apply(op, state.r.borrow_mut(), bytes@, &());
                assert(state.data@ == state.r@.read@);
            }

            handle.release_write(state);

            Tracked(complete)
        }

        exec fn flush<Lin>(&self, Tracked(lin): Tracked<Lin>) -> (Tracked<Lin::Completion>)
            where
                Lin: ReadLinearizer<Flush>,
        {
            let ghost op = Flush{ read_id: self.read_id(), durable_id: self.durable_id() };
            let handle = self.lk.acquire_read();
            let state = handle.borrow();

            let tracked complete;
            proof {
                complete = lin.apply(op, state.r.borrow(), &());
            }

            handle.release_read();

            Tracked(complete)
        }
    }
}
