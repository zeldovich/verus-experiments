use vstd::prelude::*;
use vstd::logatom::*;

use sl::seq_view::*;
use sl::seq_helper::*;

use super::pmem::*;
use super::pmem_impl::*;

verus! {
    struct Resources {
        read: SeqFrac<u8>,
        durable: SeqFrac<u8>,
    }

    impl MutLinearizer<Write> for Resources {
        type Completion = Resources;

        closed spec fn pre(self, op: Write) -> bool {
            &&& self.read.valid(op.read_id)
            &&& self.durable.valid(op.durable_id)

            &&& self.read.off() == self.durable.off()
            &&& self.read@.len() == self.durable@.len()

            &&& op.data.len() > 0
            &&& self.read.off() <= op.addr
            &&& op.addr + op.data.len() <= self.read.off() + self.read@.len()
        }

        closed spec fn post(self, op: Write, e: <Write as MutOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r.read.valid(op.read_id)
            &&& r.durable.valid(op.durable_id)

            &&& r.read.off() == self.read.off()
            &&& r.durable.off() == self.durable.off()

            &&& r.read@ == update_seq(self.read@, op.addr as int - self.read.off(), op.data)
            &&& can_result_from_write(r.durable@, self.durable@, op.addr as int - self.durable.off(), op.data)
        }

        proof fn apply(tracked self, op: Write, tracked r: &mut <Write as MutOperation>::Resource, new_state: <Write as MutOperation>::NewState, e: &<Write as MutOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;

            mself.read.agree(&r.read);
            mself.durable.agree(&r.durable);

            mself.read.update_range(&mut r.read, op.addr as int - mself.read.off(), op.data);
            mself.durable.update_range(&mut r.durable, op.addr as int - mself.durable.off(), new_state);

            assert(r.read@ == update_seq(old(r).read@, op.addr as int, op.data));
            assert(r.durable@ == update_seq(old(r).durable@, op.addr as int, new_state));

            mself
        }

        proof fn peek(tracked &self, op: Write, tracked r: &<Write as MutOperation>::Resource) {
            self.read.agree(&r.read);
        }
    }

    impl ReadLinearizer<Flush> for Resources {
        type Completion = Resources;

        closed spec fn pre(self, op: Flush) -> bool {
            &&& self.read.valid(op.read_id)
            &&& self.durable.valid(op.durable_id)

            &&& self.read.off() == self.durable.off()
            &&& self.read@.len() == self.durable@.len()
        }

        closed spec fn post(self, op: Flush, e: <Flush as ReadOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r == self
            &&& r.read@ == r.durable@
        }

        proof fn apply(tracked self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource, e: &<Flush as ReadOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;

            mself.read.agree(&r.read);
            mself.durable.agree(&r.durable);
            assert(mself.read@ == mself.durable@);

            mself
        }

        proof fn peek(tracked &self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource) {
        }
    }

    impl ReadLinearizer<Read> for Resources {
        type Completion = Resources;

        closed spec fn pre(self, op: Read) -> bool {
            &&& self.read.valid(op.read_id)

            &&& op.num_bytes > 0
            &&& self.read.off() <= op.addr
            &&& op.addr + op.num_bytes <= self.read.off() + self.read@.len()
        }

        closed spec fn post(self, op: Read, e: <Read as ReadOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r == self
            &&& e@ == r.read@.subrange(op.addr as int - r.read.off(), op.addr as int - r.read.off() + op.num_bytes as int)
        }

        proof fn apply(tracked self, op: Read, tracked r: &<Read as ReadOperation>::Resource, e: &<Read as ReadOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;

            mself.read.agree(r);

            assert(e@ == mself.read@.subrange(op.addr as int - mself.read.off(), op.addr as int - mself.read.off() + op.num_bytes as int));
            mself
        }

        proof fn peek(tracked &self, op: Read, tracked r: &<Read as ReadOperation>::Resource) {
            self.read.agree(r);
            assert(op.peek_ensures(*r));
        }
    }

    fn test() {
        let (sm, Tracked(r), Tracked(d)) = SimpleMem::new(1024);
        let tracked res = Resources{
            read: r,
            durable: d,
        };
        let Tracked(res) = sm.write::<Resources>(0, &[0, 1, 2, 3], Tracked(res));
        assert(res.read@[0] == 0);
        let Tracked(res) = sm.write::<Resources>(4, &[4, 5, 6, 7], Tracked(res));
        assert(res.read@[4] == 4);
        let (rvec, Tracked(res)) = sm.read::<Resources>(2, 4, Tracked(res));
        assert(rvec@ == seq![2u8, 3, 4, 5]);
        let Tracked(res) = sm.flush::<Resources>(Tracked(res));

        assert(res.read@[4] == 4);
        assert(res.durable@[4] == 4);
    }
}
