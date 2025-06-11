use vstd::prelude::*;
use vstd::logatom::*;
use vstd::tokens::frac::*;

use sl::seq_view::*;

use super::pmem::*;

verus! {
    pub struct Fracs {
        pub read: SeqFrac<u8>,
        pub durable: GhostVar<Seq<u8>>,
    }

    impl MutLinearizer<Write> for Fracs {
        type Completion = Fracs;

        open spec fn pre(self, op: Write) -> bool {
            &&& self.read.valid(op.read_id)
            &&& self.durable.id() == op.durable_id

            &&& op.data.len() > 0
            &&& self.read.off() <= op.addr
            &&& op.addr + op.data.len() <= self.read.off() + self.read@.len()
        }

        open spec fn post(self, op: Write, e: <Write as MutOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r.read.valid(op.read_id)
            &&& r.durable.id() == op.durable_id

            &&& r.read.off() == self.read.off()

            &&& r.read@ == self.read@.update_subrange_with(op.addr - self.read.off(), op.data)
            &&& can_result_from_write(r.durable@, self.durable@, op.addr as int, op.data)
        }

        proof fn apply(tracked self, op: Write, tracked r: &mut <Write as MutOperation>::Resource, new_state: <Write as MutOperation>::NewState, e: &<Write as MutOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;

            mself.read.agree(&r.read);
            r.durable.agree(&mself.durable);

            mself.read.update_subrange_with(&mut r.read, op.addr as int - mself.read.off(), op.data);
            r.durable.update(&mut mself.durable, r.durable@.update_subrange_with(op.addr as int, new_state));

            mself
        }

        proof fn peek(tracked &self, op: Write, tracked r: &<Write as MutOperation>::Resource) {
            self.read.agree(&r.read);
        }
    }

    impl ReadLinearizer<Flush> for Fracs {
        type Completion = Fracs;

        open spec fn pre(self, op: Flush) -> bool {
            &&& self.read.valid(op.read_id)
            &&& self.durable.id() == op.durable_id
        }

        open spec fn post(self, op: Flush, e: <Flush as ReadOperation>::ExecResult, r: Self::Completion) -> bool {
            &&& r == self
            &&& r.read@.len() > 0 ==> r.read@ == r.durable@.subrange(r.read.off() as int, r.read.off() + r.read@.len() as int)
        }

        proof fn apply(tracked self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource, e: &<Flush as ReadOperation>::ExecResult) -> tracked Self::Completion {
            let tracked mut mself = self;

            mself.read.agree(&r.read);
            r.durable.agree(&mself.durable);

            mself
        }

        proof fn peek(tracked &self, op: Flush, tracked r: &<Flush as ReadOperation>::Resource) {
        }
    }

    impl ReadLinearizer<Read> for Fracs {
        type Completion = Fracs;

        open spec fn pre(self, op: Read) -> bool {
            &&& self.read.valid(op.read_id)

            &&& op.num_bytes > 0
            &&& self.read.off() <= op.addr
            &&& op.addr + op.num_bytes <= self.read.off() + self.read@.len()
        }

        open spec fn post(self, op: Read, e: <Read as ReadOperation>::ExecResult, r: Self::Completion) -> bool {
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
}
