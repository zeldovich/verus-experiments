use builtin::*;
use vstd::prelude::*;
use vstd::modes::*;
use vstd::invariant::*;
use std::sync::Arc;

mod disk;

use disk::DiskView;
use disk::MemCrashView;
use disk::view_write;
use disk::frac;
use frac::FractionalResource;
use disk::Disk;
use disk::DiskWritePermission;
use disk::DiskBarrierPermission;
use disk::DISK_INV_NS;

verus! {
    pub type AbsView = u8;

    pub open spec fn abs_inv(abs: AbsView, disk: DiskView) -> bool
    {
        abs == disk.0 && disk.0 <= disk.1
    }

    pub struct AbsPair {
        mem: AbsView,
        crash: AbsView,
    }

    struct DiskInvState {
        // Actual disk state.
        disk: Option<FractionalResource<MemCrashView, 2>>,

        // Re-exporting disk state for applicaton to track intermediate writes.
        disk2: Option<FractionalResource<MemCrashView, 2>>,

        // Abstract state (memory and crash).
        abs: Option<FractionalResource<AbsPair, 2>>,
    }

    struct DiskInvParam {
        disk_id: int,
        disk2_id: int,
        abs_id: int,
    }

    struct DiskInvPred {}

    impl InvariantPredicate<DiskInvParam, DiskInvState> for DiskInvPred
    {
        closed spec fn inv(k: DiskInvParam, v: DiskInvState) -> bool {
            v.disk.is_Some() &&
            v.disk2.is_Some() &&
            v.abs.is_Some() &&
            v.disk.unwrap().inv() &&
            v.disk2.unwrap().inv() &&
            v.abs.unwrap().inv() &&
            v.disk.unwrap().id() == k.disk_id &&
            v.disk2.unwrap().id() == k.disk2_id &&
            v.abs.unwrap().id() == k.abs_id &&
            v.disk.unwrap().frac() == 1 &&
            v.disk2.unwrap().frac() == 1 &&
            v.abs.unwrap().frac() == 1 &&
            v.disk.unwrap().val() == v.disk2.unwrap().val() &&
            abs_inv(v.abs.unwrap().val().mem, v.disk.unwrap().val().mem) &&
            abs_inv(v.abs.unwrap().val().crash, v.disk.unwrap().val().crash)
        }
    }

    pub struct InvWritePerm
    {
        a: u8,
        v: u8,
        tracked disk2_frac: Option<FractionalResource<MemCrashView, 2>>,
        tracked app_frac: Option<FractionalResource<AbsPair, 2>>,
        ghost invoked: bool,
        ghost pre: (MemCrashView, AbsPair, DiskInvParam),
        inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
    }

    impl DiskWritePermission<(MemCrashView, AbsPair, DiskInvParam)> for InvWritePerm
    {
        closed spec fn inv(&self) -> bool {
            self.disk2_frac.is_Some() &&
            self.disk2_frac.unwrap().inv() &&
            self.disk2_frac.unwrap().frac() == 1 &&
            self.disk2_frac.unwrap().id() == self.inv.constant().disk2_id &&
            self.disk2_frac.unwrap().val().mem == if !self.invoked() { self.pre.0.mem } else { view_write(self.pre.0.mem, self.addr(), self.val()) } &&
            ( self.disk2_frac.unwrap().val().crash == self.pre.0.crash ||
              ( self.invoked() && self.disk2_frac.unwrap().val().crash == view_write(self.pre.0.crash, self.addr(), self.val()) ) ) &&

            self.app_frac.is_Some() &&
            self.app_frac.unwrap().inv() &&
            self.app_frac.unwrap().frac() == 1 &&
            self.app_frac.unwrap().id() == self.inv.constant().abs_id &&
            self.app_frac.unwrap().val().mem == if !self.invoked() || self.addr() != 0 { self.pre.1.mem } else { self.val() } &&
            ( self.app_frac.unwrap().val().crash == self.pre.1.crash ||
              ( self.invoked() && self.addr() == 0 && self.app_frac.unwrap().val().crash == self.val() ) ) &&

            self.inv.namespace() == DISK_INV_NS &&
            self.inv.constant() == self.pre.2 &&

            if self.addr() == 0 {
                self.val() <= self.disk2_frac.unwrap().val().mem.1 &&
                self.val() <= self.disk2_frac.unwrap().val().crash.1
            } else {
                self.val() >= self.disk2_frac.unwrap().val().mem.0 &&
                self.val() >= self.disk2_frac.unwrap().val().crash.0
            }
        }

        closed spec fn id(&self) -> int {
            self.inv.constant().disk_id
        }

        closed spec fn addr(&self) -> u8 {
            self.a
        }

        closed spec fn val(&self) -> u8 {
            self.v
        }

        closed spec fn invoked(&self) -> bool {
            self.invoked
        }

        closed spec fn pre(&self) -> (MemCrashView, AbsPair, DiskInvParam) {
            self.pre
        }

        proof fn apply(tracked &mut self, tracked r: FractionalResource<MemCrashView, 2>, write_crash: bool, tracked credit: OpenInvariantCredit) -> (tracked result: FractionalResource<MemCrashView, 2>)
        {
            self.invoked = true;

            let tracked mut r1opt: Option<FractionalResource<MemCrashView, 2>> = None;
            open_atomic_invariant!(credit => &self.inv => inner => {
                let tracked mut opt_frac_disk = None;
                tracked_swap(&mut inner.disk, &mut opt_frac_disk);
                let tracked r = r.combine(opt_frac_disk.tracked_unwrap());
                let tracked r = r.update(MemCrashView{
                        mem: view_write(r.val().mem, self.addr(), self.val()),
                        crash: if write_crash { view_write(r.val().crash, self.addr(), self.val()) } else { r.val().crash },
                    });
                let tracked (r1, r2) = r.split(1);
                inner.disk = Some(r2);

                let tracked mut opt_frac_disk2 = None;
                tracked_swap(&mut inner.disk2, &mut opt_frac_disk2);
                let tracked mut opt_frac_disk2_self = None;
                tracked_swap(&mut self.disk2_frac, &mut opt_frac_disk2_self);
                let tracked r2 = opt_frac_disk2.tracked_unwrap();
                let tracked r2 = r2.combine(opt_frac_disk2_self.tracked_unwrap());
                let tracked r2 = r2.update(r1.val());
                let tracked (r21, r22) = r2.split(1);
                self.disk2_frac = Some(r21);
                inner.disk2 = Some(r22);

                if self.addr() == 0 {
                    let tracked mut opt_frac_abs = None;
                    tracked_swap(&mut inner.abs, &mut opt_frac_abs);
                    let tracked mut opt_frac_abs_self = None;
                    tracked_swap(&mut self.app_frac, &mut opt_frac_abs_self);
                    let tracked abs = opt_frac_abs.tracked_unwrap();
                    let tracked abs = abs.combine(opt_frac_abs_self.tracked_unwrap());
                    let tracked abs = abs.update(AbsPair{
                        mem: self.val(),
                        crash: if write_crash { self.val() } else { abs.val().crash },
                    });
                    let tracked (abs1, abs2) = abs.split(1);
                    self.app_frac = Some(abs1);
                    inner.abs = Some(abs2)
                };

                r1opt = Some(r1)
            });

            r1opt.tracked_unwrap()
        }
    }

    impl InvWritePerm
    {
        proof fn alloc(tracked addr: u8, tracked val: u8, tracked inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>, tracked dfrac: FractionalResource<MemCrashView, 2>, tracked afrac: FractionalResource<AbsPair, 2>) -> (tracked res: InvWritePerm)
            requires
                dfrac.inv(),
                dfrac.frac() == 1,
                dfrac.id() == inv.constant().disk2_id,
                afrac.inv(),
                afrac.frac() == 1,
                afrac.id() == inv.constant().abs_id,
                if addr == 0 {
                    val <= dfrac.val().mem.1 && val <= dfrac.val().crash.1
                } else {
                    val >= dfrac.val().mem.0 && val >= dfrac.val().crash.0
                },
                inv.namespace() == DISK_INV_NS,
            ensures
                res.inv(),
                !res.invoked(),
                res.id() == inv.constant().disk_id,
                res.addr() == addr,
                res.val() == val,
                res.pre() == (dfrac.val(), afrac.val(), inv.constant()),
        {
            let tracked mut f = InvWritePerm{
                a: addr,
                v: val,
                disk2_frac: Some(dfrac),
                app_frac: Some(afrac),
                invoked: false,
                pre: (dfrac.val(), afrac.val(), inv.constant()),
                inv: inv,
            };
            f
        }

        proof fn frac(tracked self) -> (tracked res: (Option<FractionalResource<MemCrashView, 2>>, Option<FractionalResource<AbsPair, 2>>))
            requires
                self.invoked(),
                self.inv(),
            ensures
                res.0.is_Some(),
                res.1.is_Some(),
                res.0.unwrap().inv(),
                res.1.unwrap().inv(),
                res.0.unwrap().frac() == 1,
                res.1.unwrap().frac() == 1,
                res.0.unwrap().id() == self.pre().2.disk2_id,
                res.1.unwrap().id() == self.pre().2.abs_id,
                res.0.unwrap().val().mem == view_write(self.pre().0.mem, self.addr(), self.val()),
                ( res.0.unwrap().val().crash == self.pre().0.crash ||
                  res.0.unwrap().val().crash == view_write(self.pre().0.crash, self.addr(), self.val()) ),
                res.1.unwrap().val().mem == if self.addr() == 0 { self.val() } else { self.pre().1.mem },
                ( res.1.unwrap().val().crash == self.pre().1.crash ||
                  ( self.addr() == 0 && res.1.unwrap().val().crash == self.val() ) )
        {
            (self.disk2_frac, self.app_frac)
        }
    }

    pub struct InvBarrierPerm
    {
        tracked disk2_frac: Option<FractionalResource<MemCrashView, 2>>,
        tracked app_frac: Option<FractionalResource<AbsPair, 2>>,
        ghost invoked: bool,
        ghost pre: (MemCrashView, AbsPair, DiskInvParam),
        inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>,
    }

    impl DiskBarrierPermission<(MemCrashView, AbsPair, DiskInvParam)> for InvBarrierPerm
    {
        closed spec fn inv(&self) -> bool {
            self.disk2_frac.is_Some() &&
            self.disk2_frac.unwrap().inv() &&
            self.disk2_frac.unwrap().frac() == 1 &&
            self.disk2_frac.unwrap().id() == self.inv.constant().disk2_id &&
            self.disk2_frac.unwrap().val() == self.pre.0 &&

            self.app_frac.is_Some() &&
            self.app_frac.unwrap().inv() &&
            self.app_frac.unwrap().frac() == 1 &&
            self.app_frac.unwrap().id() == self.inv.constant().abs_id &&
            self.app_frac.unwrap().val() == self.pre.1 &&

            self.inv.namespace() == DISK_INV_NS &&
            self.inv.constant() == self.pre.2 &&

            if self.invoked() {
                self.disk2_frac.unwrap().val().mem == self.disk2_frac.unwrap().val().crash &&
                self.app_frac.unwrap().val().mem == self.app_frac.unwrap().val().crash
            } else {
                true
            }
        }

        closed spec fn id(&self) -> int {
            self.inv.constant().disk_id
        }

        closed spec fn invoked(&self) -> bool {
            self.invoked
        }

        closed spec fn pre(&self) -> (MemCrashView, AbsPair, DiskInvParam) {
            self.pre
        }

        proof fn apply(tracked &mut self, tracked r: FractionalResource<MemCrashView, 2>, tracked credit: OpenInvariantCredit) -> (tracked result: FractionalResource<MemCrashView, 2>)
        {
            self.invoked = true;

            let tracked mut r = r;
            open_atomic_invariant!(credit => &self.inv => inner => {
                let tracked mut opt_frac_disk = None;
                tracked_swap(&mut inner.disk, &mut opt_frac_disk);
                let tracked frac_disk = opt_frac_disk.tracked_unwrap();
                r.agree(&frac_disk);
                inner.disk = Some(frac_disk);

                let tracked mut opt_frac_disk2 = None;
                tracked_swap(&mut inner.disk2, &mut opt_frac_disk2);
                let tracked frac_disk2 = opt_frac_disk2.tracked_unwrap();
                let tracked mut opt_frac_disk2_self = None;
                tracked_swap(&mut self.disk2_frac, &mut opt_frac_disk2_self);
                let tracked mut self_disk2 = opt_frac_disk2_self.tracked_unwrap();
                self_disk2.agree(&frac_disk2);
                inner.disk2 = Some(frac_disk2);
                self.disk2_frac = Some(self_disk2);

                let tracked mut opt_frac_abs = None;
                tracked_swap(&mut inner.abs, &mut opt_frac_abs);
                let tracked mut frac_abs = opt_frac_abs.tracked_unwrap();
                let tracked mut opt_frac_abs_self = None;
                tracked_swap(&mut self.app_frac, &mut opt_frac_abs_self);
                let tracked mut self_abs = opt_frac_abs_self.tracked_unwrap();
                self_abs.agree(&frac_abs);
                inner.abs = Some(frac_abs);
                self.app_frac = Some(self_abs)
            });

            r
        }
    }

    impl InvBarrierPerm
    {
        proof fn alloc(tracked inv: Arc<AtomicInvariant<DiskInvParam, DiskInvState, DiskInvPred>>, tracked dfrac: FractionalResource<MemCrashView, 2>, tracked afrac: FractionalResource<AbsPair, 2>) -> (tracked res: InvBarrierPerm)
            requires
                dfrac.inv(),
                dfrac.frac() == 1,
                dfrac.id() == inv.constant().disk2_id,
                afrac.inv(),
                afrac.frac() == 1,
                afrac.id() == inv.constant().abs_id,
                inv.namespace() == DISK_INV_NS,
            ensures
                res.inv(),
                !res.invoked(),
                res.id() == inv.constant().disk_id,
                res.pre() == (dfrac.val(), afrac.val(), inv.constant()),
        {
            let tracked mut f = InvBarrierPerm{
                disk2_frac: Some(dfrac),
                app_frac: Some(afrac),
                invoked: false,
                pre: (dfrac.val(), afrac.val(), inv.constant()),
                inv: inv,
            };
            f
        }

        proof fn frac(tracked self) -> (tracked res: (Option<FractionalResource<MemCrashView, 2>>, Option<FractionalResource<AbsPair, 2>>))
            requires
                self.invoked(),
                self.inv(),
            ensures
                res.0.is_Some(),
                res.1.is_Some(),
                res.0.unwrap().inv(),
                res.1.unwrap().inv(),
                res.0.unwrap().frac() == 1,
                res.1.unwrap().frac() == 1,
                res.0.unwrap().id() == self.pre().2.disk2_id,
                res.1.unwrap().id() == self.pre().2.abs_id,
                res.0.unwrap().val() == self.pre().0 &&
                res.0.unwrap().val().mem == res.0.unwrap().val().crash &&
                res.1.unwrap().val() == self.pre().1 &&
                res.1.unwrap().val().mem == res.1.unwrap().val().crash
        {
            (self.disk2_frac, self.app_frac)
        }
    }

    fn main()
    {
        let (mut d, Tracked(r)) = Disk::alloc();

        let tracked app_r = FractionalResource::<AbsPair, 2>::alloc(AbsPair{ mem: 0, crash: 0 });
        let tracked (app_r, app_r1) = app_r.split(1);

        let tracked disk_r = FractionalResource::<MemCrashView, 2>::alloc(r.val());
        let tracked (disk_r, disk_r1) = disk_r.split(1);

        let ghost inv_param = DiskInvParam{
            disk_id: r.id(),
            disk2_id: disk_r1.id(),
            abs_id: app_r1.id(),
        };

        let tracked inv_st = DiskInvState{
            disk: Some(r),
            disk2: Some(disk_r1),
            abs: Some(app_r1),
        };

        let tracked i = AtomicInvariant::<_, _, DiskInvPred>::new(inv_param, inv_st, disk::DISK_INV_NS as int);
        let tracked i = Arc::new(i);

        // let x0 = d.read(0, Tracked(&mut r));
        // let x1 = d.read(1, Tracked(&mut r));
        // assert(x0 == 0 && x1 == 0);

        let tracked fupd = InvWritePerm::alloc(1u8, 5u8, i.clone(), disk_r, app_r);
        d.write::<_, InvWritePerm>(1, 5, Tracked(&mut fupd));
        let tracked (disk_r, app_r) = fupd.frac();
        let tracked disk_r = disk_r.tracked_unwrap();
        let tracked app_r = app_r.tracked_unwrap();

        // let x0 = d.read(0, Tracked(&mut r));
        // let x1 = d.read(1, Tracked(&mut r));
        // assert(x0 == 0 && x1 == 5);

        // Main point: commenting out this line makes the proof fail because
        // we might end up in a crash state where the first write (above)
        // didn't happen but the second write (below) does happen, and that
        // violates the invariant that block0 <= block1.
        let tracked fupd = InvBarrierPerm::alloc(i.clone(), disk_r, app_r);
        d.barrier::<_, InvBarrierPerm>(Tracked(&mut fupd));
        let tracked (disk_r, app_r) = fupd.frac();
        let tracked disk_r = disk_r.tracked_unwrap();
        let tracked app_r = app_r.tracked_unwrap();

        let tracked fupd = InvWritePerm::alloc(0u8, 2u8, i.clone(), disk_r, app_r);
        d.write::<_, InvWritePerm>(0, 2, Tracked(&mut fupd));
        let tracked (disk_r, app_r) = fupd.frac();
        let tracked disk_r = disk_r.tracked_unwrap();
        let tracked app_r = app_r.tracked_unwrap();

        // let x0 = d.read(0, Tracked(&mut r));
        // let x1 = d.read(1, Tracked(&mut r));
        // assert(x0 == 2 && x1 == 5);

        ()
    }
}
