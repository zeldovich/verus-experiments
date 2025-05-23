use builtin::*;
use vstd::prelude::*;
use vstd::logatom;
use vstd::tokens::frac::{GhostVar, GhostVarAuth};

use sl::pairdisk::DiskView;
use sl::pairdisk::MemCrashView;
use sl::pairdisk::view_write;
use sl::pairdisk::Disk;
use sl::pairdisk::DiskWriteOp;

verus! {
    pub type AbsView = u8;

    pub open spec fn abs_inv(abs: AbsView, disk: DiskView) -> bool
    {
        abs == disk.0 && disk.0 <= disk.1
    }

    pub struct WriteFupd
    {
        pub tracked frac: GhostVar<MemCrashView>,
        pub ghost abs_pre: AbsView,
        pub ghost abs_post: AbsView,
    }

    impl logatom::MutLinearizer<DiskWriteOp> for WriteFupd
    {
        type Completion = GhostVar<MemCrashView>;

        open spec fn pre(self, op: DiskWriteOp) -> bool {
            &&& self.frac.id() == op.id
            &&& if op.addr == 0 {
                    self.abs_post == op.val &&
                    op.val <= self.frac@.mem.1 &&
                    op.val <= self.frac@.crash.1
                } else {
                    self.abs_post == self.abs_pre &&
                    op.val >= self.abs_pre
                }
            &&& abs_inv(self.abs_pre, self.frac@.mem)
            &&& abs_inv(self.abs_pre, self.frac@.crash)
        }

        open spec fn post(self, op: DiskWriteOp, er: (), r: GhostVar<MemCrashView>) -> bool {
            &&& r.id() == op.id
            &&& r@.mem == view_write(self.frac@.mem, op.addr, op.val)
            &&& ( r@.crash == self.frac@.crash ||
                  r@.crash == view_write(self.frac@.crash, op.addr, op.val) )
            &&& abs_inv(self.abs_post, r@.mem)
            &&& ( abs_inv(self.abs_pre, r@.crash) ||
                  abs_inv(self.abs_post, r@.crash) )
        }

        proof fn apply(tracked self, op: DiskWriteOp, tracked r: &mut GhostVarAuth<MemCrashView>, write_crash: bool, er: &()) -> (tracked result: GhostVar<MemCrashView>)
        {
            let tracked mut f = self.frac;
            r.update(&mut f, MemCrashView{
                    mem: view_write(r@.mem, op.addr, op.val),
                    crash: if write_crash { view_write(r@.crash, op.addr, op.val) } else { r@.crash },
                });
            assert(f.id() == op.id);
            assert(f@.mem == view_write(self.frac@.mem, op.addr, op.val));
            assert(self.post(op, *er, f));
            f
        }

        proof fn peek(tracked &self, op: DiskWriteOp, tracked r: &GhostVarAuth<MemCrashView>) {}
    }

    pub struct WriteFupd1
    {
        pub tracked frac: GhostVar<MemCrashView>,
        pub ghost abs: AbsView,
    }

    impl logatom::MutLinearizer<DiskWriteOp> for WriteFupd1
    {
        type Completion = GhostVar<MemCrashView>;

        open spec fn pre(self, op: DiskWriteOp) -> bool {
            &&& self.frac.id() == op.id
            &&& op.addr == 1
            &&& op.val >= self.abs
            &&& abs_inv(self.abs, self.frac@.mem)
            &&& abs_inv(self.abs, self.frac@.crash)
        }

        open spec fn post(self, op: DiskWriteOp, er: (), r: GhostVar<MemCrashView>) -> bool {
            &&& r.id() == op.id
            &&& r@.mem == view_write(self.frac@.mem, op.addr, op.val)
            &&& ( r@.crash == self.frac@.crash ||
                  r@.crash == view_write(self.frac@.crash, 1, op.val) )
            &&& abs_inv(self.abs, r@.mem)
            &&& abs_inv(self.abs, r@.crash)
        }

        proof fn apply(tracked self, op: DiskWriteOp, tracked r: &mut GhostVarAuth<MemCrashView>, write_crash: bool, er: &()) -> (tracked result: GhostVar<MemCrashView>)
        {
            let tracked mut f = self.frac;
            r.update(&mut f, MemCrashView{
                    mem: view_write(r@.mem, op.addr, op.val),
                    crash: if write_crash { view_write(r@.crash, op.addr, op.val) } else { r@.crash },
                });
            f
        }

        proof fn peek(tracked &self, op: DiskWriteOp, tracked r: &GhostVarAuth<MemCrashView>) {}
    }

    fn main()
    {
        let (mut d, Tracked(r)) = Disk::new();

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 0);

        let tracked fupd = WriteFupd{ frac: r, abs_pre: 0, abs_post: 0 };
        let Tracked(r) = d.write::<WriteFupd>(1, 5, Tracked(fupd));

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 5);

        // As another example, could use a different fupd to justify the write.
        let tracked fupd = WriteFupd1{ frac: r, abs: 0 };
        let Tracked(r) = d.write::<WriteFupd1>(1, 7, Tracked(fupd));

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 0 && x1 == 7);

        // Main point: commenting out this line makes the proof fail because
        // we might end up in a crash state where the first write (above)
        // didn't happen but the second write (below) does happen, and that
        // violates the invariant that block0 <= block1.
        d.barrier_owned(Tracked(&r));

        let tracked fupd = WriteFupd{ frac: r, abs_pre: 0, abs_post: 2 };
        let Tracked(r) = d.write::<WriteFupd>(0, 2, Tracked(fupd));

        let x0 = d.read_owned(0, Tracked(&mut r));
        let x1 = d.read_owned(1, Tracked(&mut r));
        assert(x0 == 2 && x1 == 7);

        ()
    }
}
