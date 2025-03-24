mod inv;

use std::sync::Arc;

use sl::vecdisk::*;
use sl::disk_wrap::*;
use sl::seq_view::*;
use sl::frac::*;
use sl::disk_wrap_lib::*;

use inv::*;

use vstd::prelude::*;
use vstd::invariant::*;

verus! {
    // Test of separation-logic interface with invariant ownership of crash (persist) resources.
    //
    // test_inv_init() sets up the disk and allocates the invariant for the first time, like mkfs.
    //
    // test_inv_recover() recovers from a crash on a disk that already was initialized.
    fn test_inv_init() {
        let d = Disk::new(5);
        let (mut dw, Tracked(mut f), Tracked(mut pf)) = DiskWrap::new(d);

        let Tracked(f_pf) = dw.write(0, &[0, 5, 5, 3, 7], OwningWriter::new(Tracked(f), Tracked(pf)));
        let tracked (mut f, mut pf) = f_pf;
        dw.flush(OwningFlush::new(Tracked(&f), Tracked(&pf)));

        let tracked mut f1 = f.split(1);
        let tracked mut pf1 = pf.split(1);

        let tracked mut f3 = f1.split(2);
        let tracked mut pf3 = pf1.split(2);

        let tracked mut ps = Frac::new(PtrState::A);

        let tracked crashstate = DiskCrashState{
            ptr: pf,
            a: pf1,
            b: pf3,
            ptr_state: ps.split(1),
        };

        let ghost iparam = DiskInvParam{
            persist_id: pf.id(),
            ptr_state_id: ps.id(),
        };

        let tracked i = AtomicInvariant::<_, _, DiskInvParam>::new(iparam, crashstate, 12345);
        let tracked i = Arc::new(i);

        // Help instantiate triggers later.
        assert(dw.persist_id() == i.constant().persist_id);

        // Write new data to area B; allowed because it's not the active area.
        let Tracked(mut f3) = dw.write(3, &[1, 9], InactiveWriter::new(Tracked(f3), Tracked(&ps), Tracked(&i)));

        // Flush the new data in area B so it's ready to commit.
        let Tracked(ps) = dw.flush(PreparingFlush::new(Tracked(ps), Tracked(&f3), Tracked(&i)));

        // Flip the pointer: either area A or B could be there on crash, and either is valid.
        let Tracked(f_ps) = dw.write(0, &[1], CommittingWriter::new(Tracked(f), Tracked(ps), Tracked(&i)));
        let tracked (mut f, mut ps) = f_ps;
        assert(ps@ == PtrState::Either);

        // Flush the pointer, so we know it's definitely area B that's durable now.
        let Tracked(ps) = dw.flush(CommittingFlush::new(Tracked(ps), Tracked(&f), Tracked(&i)));
        assert(ps@ == PtrState::B);

        // Temporarily write bogus data to area A, but it doesn't matter because it's not active.
        // Then write valid data.
        let Tracked(mut f1) = dw.write(1, &[0, 0], InactiveWriter::new(Tracked(f1), Tracked(&ps), Tracked(&i)));
        let Tracked(mut f1) = dw.write(1, &[2, 8], InactiveWriter::new(Tracked(f1), Tracked(&ps), Tracked(&i)));

        // Flush the new contents of area A before commit.
        let Tracked(ps) = dw.flush(PreparingFlush::new(Tracked(ps), Tracked(&f1), Tracked(&i)));

        // Write and commit the pointer, switching back to area A.
        let Tracked(f_ps) = dw.write(0, &[0], CommittingWriter::new(Tracked(f), Tracked(ps), Tracked(&i)));
        let tracked (mut f, mut ps) = f_ps;
        assert(ps@ == PtrState::Either);

        let Tracked(ps) = dw.flush(CommittingFlush::new(Tracked(ps), Tracked(&f), Tracked(&i)));
        assert(ps@ == PtrState::A);
    }

    // CORE ASSUMPTION: the disk contains state that satisfied our invariant before crash.
    #[verifier::external_body]
    proof fn disk_recovery_axiom_helper(tracked pf: SeqFrac<u8>) -> (tracked result: AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>)
        requires
            // Not a complete set of preconditions for soundness; requires trusting caller too.
            pf.inv(),
            pf.off() == 0,
            pf@.len() >= 5,
        ensures
            // Core postcondition: the invariant talks about contents of the recovered disk!
            result.constant().persist_id == pf.id(),
    {
        unimplemented!();
    }

    // CORE ASSUMPTION: we can get a disk object and an invariant that talks about that disk's
    // persistent state.
    fn disk_recovery_axiom() -> (result: (DiskWrap, Tracked<SeqFrac<u8>>, Tracked<AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>>))
        ensures
            result.0.inv(),
            result.1@.valid(result.0.id()),
            result.1@.off() == 0,
            result.1@@.len() == 5,
            result.2@.constant().persist_id == result.0.persist_id(),
    {
        let d = Disk::new(5);
        let (dw, Tracked(mut f), Tracked(mut pf)) = DiskWrap::new(d);
        let tracked i = disk_recovery_axiom_helper(pf);
        (dw, Tracked(f), Tracked(i))
    }

    // Untrusted (verified) recovery helper: re-allocate ephemeral ghost state.
    fn disk_recovery_verified_helper(Tracked(i): Tracked<AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>>) -> (result: (Tracked<AtomicInvariant::<DiskInvParam, DiskCrashState, DiskInvParam>>, Tracked<Frac<PtrState>>))
        ensures
            result.1@.valid(result.0@.constant().ptr_state_id, 1),
            result.0@.constant().persist_id == i.constant().persist_id,
    {
        // Destroy the invariant; we will re-allocate a new one with a different ptr_state_id.
        let ghost mut iparam = i.constant();
        let tracked inner = i.into_inner();

        let tracked mut ps = Frac::new(inner.ptr_state@);
        proof {
            inner.ptr_state = ps.split(1);
            iparam.ptr_state_id = ps.id();
        }

        // Allocate a new invariant.
        let tracked i = AtomicInvariant::<_, _, DiskInvParam>::new(iparam, inner, i.namespace());

        (Tracked(i), Tracked(ps))
    }

    fn test_inv_recover() {
        let (mut dw, Tracked(mut f), Tracked(i)) = disk_recovery_axiom();

        // Re-allocate ptr_state_frac.
        let (Tracked(i), Tracked(mut ps)) = disk_recovery_verified_helper(Tracked(i));
        let tracked i = Arc::new(i);

        let tracked mut f1 = f.split(1);
        let tracked mut f3 = f1.split(2);

        // Superfluous flush: establish that ps@ is either A or B.
        // Really, we should know that f@ == pf@ (persistent state).
        let Tracked(ps) = dw.flush(CommittingFlush::new(Tracked(ps), Tracked(&f), Tracked(&i)));
        assert(ps@ == PtrState::A || ps@ == PtrState::B);

        let (ptr, _) = dw.read(0, 1, OwningReader::new(Tracked(&f)));
        if ptr[0] == 0 {
            assert(ps@ == PtrState::A);
        } else {
            assert(ps@ == PtrState::B);

            // Temporarily write bogus data to area A, but it doesn't matter because it's not active.
            // Then write valid data.
            let Tracked(mut f1) = dw.write(1, &[0, 0], InactiveWriter::new(Tracked(f1), Tracked(&ps), Tracked(&i)));
            let Tracked(mut f1) = dw.write(1, &[2, 8], InactiveWriter::new(Tracked(f1), Tracked(&ps), Tracked(&i)));

            // Flush the new contents of area A before commit.
            let Tracked(ps) = dw.flush(PreparingFlush::new(Tracked(ps), Tracked(&f1), Tracked(&i)));

            // Write and commit the pointer, switching back to area A.
            let Tracked(f_ps) = dw.write(0, &[0], CommittingWriter::new(Tracked(f), Tracked(ps), Tracked(&i)));
            let tracked (mut f, mut ps) = f_ps;
            assert(ps@ == PtrState::Either);

            let Tracked(ps) = dw.flush(CommittingFlush::new(Tracked(ps), Tracked(&f), Tracked(&i)));
            assert(ps@ == PtrState::A);
        }
    }

    // Lower-level test of writing to disk addresses with full ownership of crash resources.
    fn test_rw() {
        let d = Disk::new(1024);
        let (mut dw, Tracked(mut f0), Tracked(mut pf0)) = DiskWrap::new(d);

        let tracked mut f4 = f0.split(4);
        let tracked mut f8 = f4.split(4);

        let tracked mut pf4 = pf0.split(4);
        let tracked mut pf8 = pf4.split(4);

        assert(f0@ == seq![0u8, 0u8, 0u8, 0u8]);

        let tracked mut f2 = f0.split(2);
        let Tracked(f0_pf0) = dw.write(0, &[120, 121], OwningWriter::new(Tracked(f0), Tracked(pf0)));
        let tracked (mut f0, mut pf0) = f0_pf0;
        let Tracked(f2_pf0) = dw.write(2, &[122, 123], OwningWriter::new(Tracked(f2), Tracked(pf0)));
        let tracked (mut f2, mut pf0) = f2_pf0;
        proof { f0.combine(f2); }

        let Tracked(f4_pf4) = dw.write(4, &[124, 125, 126, 127], OwningWriter::new(Tracked(f4), Tracked(pf4)));
        let tracked (mut f4, mut pf4) = f4_pf4;

        assert(f0@ == seq![120u8, 121u8, 122u8, 123u8]);

        let (x, _) = dw.read(0, 4, OwningReader::new(Tracked(&f0)));
        assert(x@ == seq![120u8, 121u8, 122u8, 123u8]);
        let (x, _) = dw.read(4, 4, OwningReader::new(Tracked(&f4)));
        assert(x@ == seq![124u8, 125u8, 126u8, 127u8]);
    }

    fn main() {
        test_rw();
        test_inv_init();
        test_inv_recover();
    }
}
