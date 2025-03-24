use vstd::prelude::*;

verus! {
    pub struct T {
        a: u8,
    }

    impl T {
        #[verifier::type_invariant]
        pub closed spec fn type_inv(self) -> bool {
            self.a == 0 || self.a == 2
        }
    }

    pub fn test(r: &T) -> T {
        proof {
            use_type_invariant(r);
        };
        assert(r.a < 3);
        assert(r.a != 1);
        if r.a == 0 {
            T{ a: 2u8 }
        } else if r.a == 1 {
            T{ a: 100u8 }
        } else {
            T{ a: 0u8 }
        }
    }

    pub fn typeinv_example() {
        let x = T{a: 0u8};
        let y = test(&x);
        proof {
            use_type_invariant(y);
        };
        assert(y.a < 3);
    }
}
