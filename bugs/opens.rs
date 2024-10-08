use vstd::prelude::*;
use vstd::invariant::*;

verus! {
    trait T {
        spec fn namespace() -> int;
        fn f(&self) opens_invariants [ Self::namespace() ];
    }

    struct P {}
    impl InvariantPredicate<(), ()> for P {
        closed spec fn inv(k: (), v: ()) -> bool { true }
    }

    struct S {
        inv: AtomicInvariant<(), (), P>,
    }

    impl T for S {
        spec fn namespace() -> int { 5 }
        fn f(&self) {
            open_atomic_invariant!(&self.inv => inner => {});
        }
    }
}
