use builtin::*;
use vstd::prelude::*;
use vstd::invariant::*;
use std::sync::Arc;

use sl::frac::Frac;
use sl::logatom;
use sl::pairdisk::DiskView;
use sl::pairdisk::MemCrashView;
use sl::pairdisk::view_read;
use sl::pairdisk::view_write;
use sl::pairdisk::Disk;
use sl::pairdisk::DiskReadOp;
use sl::pairdisk::DiskWriteOp;
use sl::pairdisk::DiskBarrierOp;

verus! {
    pub type AbsView = u8;

    pub open spec fn abs_inv(abs: AbsView, disk: DiskView) -> bool
    {
        abs == disk.0 && disk.0 <= disk.1
    }

    pub struct AbsPair {
        pub mem: AbsView,
        pub crash: AbsView,
    }

    pub struct DiskInvState {
        // Actual disk state.
        disk: Frac<MemCrashView>,

        // Re-exporting disk state for applicaton to track intermediate writes.
        disk2: Frac<MemCrashView>,

        // Abstract state (memory and crash).
        abs: Frac<AbsPair>,
    }

    pub struct DiskInvParam {
        pub disk_id: int,
        pub disk2_id: int,
        pub abs_id: int,
    }

    pub struct DiskInvPred {}

    impl InvariantPredicate<DiskInvParam, DiskInvState> for DiskInvPred
    {
        closed spec fn inv(k: DiskInvParam, v: DiskInvState) -> bool {
            v.disk.valid(k.disk_id, 1) &&
            v.disk2.valid(k.disk2_id, 1) &&
            v.abs.valid(k.abs_id, 1) &&
            v.disk@ == v.disk2@ &&
            abs_inv(v.abs@.mem, v.disk@.mem) &&
            abs_inv(v.abs@.crash, v.disk@.crash)
        }
    }

    pub struct InvPermResult
    {
        pub disk2_frac: Frac<MemCrashView>,
        pub app_frac: Frac<AbsPair>,
    }

    pub struct InvWritePerm
    {
        pub a: u8,
        pub v: u8,
        pub tracked disk2_frac: Frac<MemCrashView>,
        pub tracked app_frac: Frac<AbsPair>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
        pub tracked credit: OpenInvariantCredit,
    }

    impl logatom::MutLinearizer<DiskWriteOp> for InvWritePerm
    {
        type ApplyResult = InvPermResult;

        open spec fn namespaces(self) -> Set<int> { set![self.inv.namespace()] }

        open spec fn pre(self, op: DiskWriteOp) -> bool {
            &&& op.id == self.inv.constant().disk_id
            &&& self.disk2_frac.valid(self.inv.constant().disk2_id, 1)
            &&& self.app_frac.valid(self.inv.constant().abs_id, 1)
            &&& if op.addr == 0 {
                    op.val <= self.disk2_frac@.mem.1 &&
                    op.val <= self.disk2_frac@.crash.1
                } else {
                    op.val >= self.disk2_frac@.mem.0 &&
                    op.val >= self.disk2_frac@.crash.0
                }
        }

        open spec fn post(self, op: DiskWriteOp, er: (), r: InvPermResult) -> bool {
            &&& r.disk2_frac.valid(self.inv.constant().disk2_id, 1)
            &&& r.disk2_frac@.mem == view_write(self.disk2_frac@.mem, op.addr, op.val)
            &&& ( r.disk2_frac@.crash == self.disk2_frac@.crash ||
                  r.disk2_frac@.crash == view_write(self.disk2_frac@.crash, op.addr, op.val) )

            &&& r.app_frac.valid(self.inv.constant().abs_id, 1)
            &&& r.app_frac@.mem == if op.addr == 0 { op.val } else { self.app_frac@.mem }
            &&& ( r.app_frac@.crash == self.app_frac@.crash ||
                  ( op.addr == 0 && r.app_frac@.crash == op.val ) )
        }

        proof fn apply(tracked self, op: DiskWriteOp, write_crash: bool, tracked r: &mut Frac<MemCrashView>, er: &()) -> (tracked result: InvPermResult)
        {
            let tracked mut mself = self;
            let tracked mut ires;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                r.combine(inner.disk);
                r.update(MemCrashView{
                        mem: view_write(r@.mem, op.addr, op.val),
                        crash: if write_crash { view_write(r@.crash, op.addr, op.val) } else { r@.crash },
                    });
                inner.disk = r.split(1);

                mself.disk2_frac.combine(inner.disk2);
                mself.disk2_frac.update(inner.disk@);
                inner.disk2 = mself.disk2_frac.split(1);

                if op.addr == 0 {
                    mself.app_frac.combine(inner.abs);
                    mself.app_frac.update(AbsPair{
                        mem: op.val,
                        crash: if write_crash { op.val } else { mself.app_frac@.crash },
                    });
                    inner.abs = mself.app_frac.split(1)
                };

                ires = InvPermResult{
                    disk2_frac: mself.disk2_frac,
                    app_frac: mself.app_frac,
                }
            });

            ires
        }

        proof fn peek(tracked &self, op: DiskWriteOp, tracked r: &Frac<MemCrashView>) {}
    }

    pub struct InvBarrierPerm
    {
        pub tracked disk2_frac: Frac<MemCrashView>,
        pub tracked app_frac: Frac<AbsPair>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
        pub tracked credit: OpenInvariantCredit,
    }

    impl logatom::ReadLinearizer<DiskBarrierOp> for InvBarrierPerm
    {
        type ApplyResult = InvPermResult;

        open spec fn namespaces(self) -> Set<int> { set![self.inv.namespace()] }

        open spec fn pre(self, op: DiskBarrierOp) -> bool {
            &&& self.inv.constant().disk_id == op.id
            &&& self.disk2_frac.valid(self.inv.constant().disk2_id, 1)
            &&& self.app_frac.valid(self.inv.constant().abs_id, 1)
        }

        open spec fn post(self, op: DiskBarrierOp, er: (), r: InvPermResult) -> bool {
            r.disk2_frac.valid(self.inv.constant().disk2_id, 1) &&
            r.app_frac.valid(self.inv.constant().abs_id, 1) &&

            r.disk2_frac@ == self.disk2_frac@ &&
            r.disk2_frac@.mem == r.disk2_frac@.crash &&

            r.app_frac@ == self.app_frac@ &&
            r.app_frac@.mem == r.app_frac@.crash
        }

        proof fn apply(tracked self, op: DiskBarrierOp, tracked r: &Frac<MemCrashView>, er: &()) -> (tracked result: InvPermResult)
        {
            let tracked mut mself = self;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                r.agree(&inner.disk);
                mself.disk2_frac.agree(&inner.disk2);
                mself.app_frac.agree(&inner.abs);
            });

            InvPermResult{
                disk2_frac: mself.disk2_frac,
                app_frac: mself.app_frac,
            }
        }

        proof fn peek(tracked &self, op: DiskBarrierOp, tracked r: &Frac<MemCrashView>) {}
    }

    pub struct InvReadPerm
    {
        pub tracked disk2_frac: Frac<MemCrashView>,
        pub tracked app_frac: Frac<AbsPair>,
        pub inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
        pub tracked credit: OpenInvariantCredit,
    }

    impl logatom::ReadLinearizer<DiskReadOp> for InvReadPerm
    {
        type ApplyResult = InvPermResult;

        open spec fn namespaces(self) -> Set<int> { set![self.inv.namespace()] }

        open spec fn pre(self, op: DiskReadOp) -> bool {
            &&& self.inv.constant().disk_id == op.id
            &&& self.disk2_frac.valid(self.inv.constant().disk2_id, 1)
            &&& self.app_frac.valid(self.inv.constant().abs_id, 1)
            &&& ( op.addr == 0 || op.addr == 1)
        }

        open spec fn post(self, op: DiskReadOp, v: u8, r: InvPermResult) -> bool {
            &&& r.disk2_frac.valid(self.inv.constant().disk2_id, 1)
            &&& r.app_frac.valid(self.inv.constant().abs_id, 1)

            &&& r.disk2_frac@ == self.disk2_frac@
            &&& r.app_frac@ == self.app_frac@

            &&& v == view_read(r.disk2_frac@.mem, op.addr)
        }

        proof fn apply(tracked self, op: DiskReadOp, tracked r: &Frac<MemCrashView>, v: &u8) -> (tracked result: InvPermResult)
        {
            let tracked mut mself = self;
            open_atomic_invariant_in_proof!(mself.credit => &mself.inv => inner => {
                r.agree(&inner.disk);
                mself.disk2_frac.agree(&inner.disk2);
                mself.app_frac.agree(&inner.abs);
            });

            InvPermResult{
                disk2_frac: mself.disk2_frac,
                app_frac: mself.app_frac,
            }
        }

        proof fn peek(tracked &self, op: DiskReadOp, tracked r: &Frac<MemCrashView>) {}
    }

    fn main()
    {
        let (mut d, Tracked(r)) = Disk::new();

        let tracked mut app_r = Frac::<AbsPair>::new(AbsPair{ mem: 0, crash: 0 });
        let tracked app_r1 = app_r.split(1);

        let tracked mut disk_r = Frac::<MemCrashView>::new(r@);
        let tracked disk_r1 = disk_r.split(1);

        let ghost inv_param = DiskInvParam{
            disk_id: r.id(),
            disk2_id: disk_r1.id(),
            abs_id: app_r1.id(),
        };

        let tracked inv_st = DiskInvState{
            disk: r,
            disk2: disk_r1,
            abs: app_r1,
        };

        let tracked i = AtomicInvariant::<_, _, DiskInvPred>::new(inv_param, inv_st, 12345);
        let tracked i = Arc::new(i);

        let credit = create_open_invariant_credit();
        let tracked fupd = InvReadPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let (x0, Tracked(res)) = d.read::<InvReadPerm>(0, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let credit = create_open_invariant_credit();
        let tracked fupd = InvReadPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let (x1, Tracked(res)) = d.read::<InvReadPerm>(1, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        assert(x0 == 0 && x1 == 0);

        let credit = create_open_invariant_credit();
        let tracked fupd = InvWritePerm{ a: 1u8, v: 5u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let Tracked(res) = d.write::<InvWritePerm>(1, 5, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let credit = create_open_invariant_credit();
        let tracked fupd = InvReadPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let (x0, Tracked(res)) = d.read::<InvReadPerm>(0, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let credit = create_open_invariant_credit();
        let tracked fupd = InvReadPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let (x1, Tracked(res)) = d.read::<InvReadPerm>(1, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        assert(x0 == 0 && x1 == 5);

        // Main point: commenting out this line makes the proof fail because
        // we might end up in a crash state where the first write (above)
        // didn't happen but the second write (below) does happen, and that
        // violates the invariant that block0 <= block1.
        let credit = create_open_invariant_credit();
        let tracked fupd = InvBarrierPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let Tracked(res) = d.barrier::<InvBarrierPerm>(Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let credit = create_open_invariant_credit();
        let tracked fupd = InvWritePerm{ a: 0u8, v: 2u8, disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let Tracked(res) = d.write::<InvWritePerm>(0, 2, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let credit = create_open_invariant_credit();
        let tracked fupd = InvReadPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let (x0, Tracked(res)) = d.read::<InvReadPerm>(0, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        let credit = create_open_invariant_credit();
        let tracked fupd = InvReadPerm{ disk2_frac: disk_r, app_frac: app_r, inv: i.clone(), credit: credit.get() };
        let (x1, Tracked(res)) = d.read::<InvReadPerm>(1, Tracked(fupd));
        let tracked InvPermResult{ disk2_frac: disk_r, app_frac: app_r } = res;

        assert(x0 == 2 && x1 == 5);

        ()
    }
}
