use super::disk_wrap::*;
use super::vecdisk::*;
use super::logatom::*;
use super::seq_view::*;
use super::seq_helper::*;

use vstd::prelude::*;

verus! {
    pub struct OwningReader<'a> {
        pub latest_frac: &'a SeqFrac<u8>,
    }

    impl<'a> ReadLinearizer<ReadOp> for OwningReader<'a> {
        type ApplyResult = ();

        open spec fn pre(self, op: ReadOp) -> bool {
            &&& self.latest_frac.valid(op.id)
            &&& self.latest_frac.off() <= op.addr
            &&& op.addr + op.len <= self.latest_frac.off() + self.latest_frac@.len()
        }

        open spec fn post(self, op: ReadOp, e: Vec<u8>, ar: ()) -> bool {
            &&& e@ =~= self.latest_frac@.subrange(op.addr - self.latest_frac.off(), op.addr + op.len - self.latest_frac.off())
        }

        proof fn apply(tracked self, op: ReadOp, tracked r: &SeqAuth<u8>, e: &Vec<u8>) -> (tracked result: ()) {
            self.latest_frac.agree(r);
        }

        proof fn peek(tracked &self, op: ReadOp, tracked r: &SeqAuth<u8>) {
            self.latest_frac.agree(r);
        }
    }

    impl<'a> OwningReader<'a> {
        pub fn new(Tracked(f): Tracked<&'a SeqFrac<u8>>) -> (result: Tracked<Self>)
            ensures
                result@.latest_frac == f
        {
            Tracked(Self{
                latest_frac: f,
            })
        }
    }

    pub struct OwningWriter {
        pub latest_frac: SeqFrac<u8>,
        pub persist_frac: SeqFrac<u8>,
    }

    impl MutLinearizer<WriteOp> for OwningWriter {
        type ApplyResult = (SeqFrac<u8>, SeqFrac<u8>);

        open spec fn pre(self, op: WriteOp) -> bool {
            &&& self.latest_frac.valid(op.id)
            &&& self.latest_frac.off() <= op.addr
            &&& op.addr + op.data.len() <= self.latest_frac.off() + self.latest_frac@.len()

            &&& self.persist_frac.valid(op.persist_id)
            &&& self.persist_frac.off() <= op.addr
            &&& op.addr + op.data.len() <= self.persist_frac.off() + self.persist_frac@.len()
        }

        open spec fn post(self, op: WriteOp, r: (), ar: Self::ApplyResult) -> bool {
            &&& ar.0.valid(op.id)
            &&& ar.0.off() == self.latest_frac.off()
            &&& ar.0@ == update_seq(self.latest_frac@, op.addr - self.latest_frac.off(), op.data)

            &&& ar.1.valid(op.persist_id)
            &&& ar.1.off() == self.persist_frac.off()
            &&& can_result_from_write(ar.1@, self.persist_frac@, op.addr - self.persist_frac.off(), op.data)
        }

        proof fn apply(tracked self, op: WriteOp, pstate: Seq<u8>, tracked r: &mut DiskResources, e: &()) -> (tracked out: Self::ApplyResult) {
            let tracked mut mself = self;
            mself.latest_frac.agree(&r.latest);
            mself.persist_frac.agree(&r.persist);

            mself.latest_frac.update_range(&mut r.latest, op.addr - self.latest_frac.off(), op.data);
            mself.persist_frac.update_range(&mut r.persist, op.addr - self.persist_frac.off(), pstate);

            (mself.latest_frac, mself.persist_frac)
        }

        proof fn peek(tracked &self, op: WriteOp, tracked r: &DiskResources) {
            self.latest_frac.agree(&r.latest);
        }
    }

    impl OwningWriter {
        pub fn new(Tracked(lf): Tracked<SeqFrac<u8>>, Tracked(pf): Tracked<SeqFrac<u8>>) -> (result: Tracked<Self>)
            ensures
                result@.latest_frac == lf,
                result@.persist_frac == pf,
        {
            Tracked(Self{ latest_frac: lf, persist_frac: pf })
        }
    }

    pub struct OwningFlush<'a> {
        pub latest_frac: &'a SeqFrac<u8>,
        pub persist_frac: &'a SeqFrac<u8>,
    }

    impl<'a> ReadLinearizer<FlushOp> for OwningFlush<'a> {
        type ApplyResult = ();

        open spec fn pre(self, op: FlushOp) -> bool {
            &&& self.latest_frac.valid(op.id)
            &&& self.persist_frac.valid(op.persist_id)
            &&& self.latest_frac.off() == self.persist_frac.off()
            &&& self.latest_frac@.len() == self.persist_frac@.len()
        }

        open spec fn post(self, op: FlushOp, r: (), ar: ()) -> bool {
            &&& self.latest_frac@ =~= self.persist_frac@
        }

        proof fn apply(tracked self, op: FlushOp, tracked r: &DiskResources, e: &()) -> (tracked result: ()) {
            self.latest_frac.agree(&r.latest);
            self.persist_frac.agree(&r.persist);
        }

        proof fn peek(tracked &self, op: FlushOp, tracked r: &DiskResources) {}
    }

    impl<'a> OwningFlush<'a> {
        pub fn new(Tracked(lf): Tracked<&'a SeqFrac<u8>>, Tracked(pf): Tracked<&'a SeqFrac<u8>>) -> (result: Tracked<Self>)
            ensures
                result@.latest_frac == lf,
                result@.persist_frac == pf,
        {
            Tracked(Self{
                latest_frac: lf,
                persist_frac: pf,
            })
        }
    }
}
