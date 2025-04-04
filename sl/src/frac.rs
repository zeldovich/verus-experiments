use builtin::*;
use vstd::pcm::*;
use vstd::prelude::*;
use vstd::modes::*;

// This implements a resource for fractional ownership of a ghost variable.
// The fractions are represented as some number out of a compile-time const
// TOTAL value; you can have any fractions from 1 up to TOTAL, and if you
// have TOTAL, you can update the ghost variable.

verus! {
    // Too bad that `nat` and `int` are forbidden as the type of a const generic parameter
    enum FractionalCarrier<T, const TOTAL: u64> {
        Value { v: T, n: int },
        Empty,
        Invalid,
    }

    impl<T, const TOTAL: u64> FractionalCarrier<T, TOTAL> {
        spec fn new(v: T) -> Self {
            FractionalCarrier::Value { v: v, n: TOTAL as int }
        }
    }

    impl<T, const TOTAL: u64> PCM for FractionalCarrier<T, TOTAL> {
        closed spec fn valid(self) -> bool {
            match self {
                FractionalCarrier::Invalid => false,
                FractionalCarrier::Empty => true,
                FractionalCarrier::Value { v: v, n: n } => 0 < n <= TOTAL,
            }
        }

        closed spec fn op(self, other: Self) -> Self {
            match self {
                FractionalCarrier::Invalid => FractionalCarrier::Invalid,
                FractionalCarrier::Empty => other,
                FractionalCarrier::Value { v: sv, n: sn } => match other {
                    FractionalCarrier::Invalid => FractionalCarrier::Invalid,
                    FractionalCarrier::Empty => self,
                    FractionalCarrier::Value { v: ov, n: on } => {
                        if sv != ov {
                            FractionalCarrier::Invalid
                        } else if sn <= 0 || on <= 0 {
                            FractionalCarrier::Invalid
                        } else {
                            FractionalCarrier::Value { v: sv, n: sn+on }
                        }
                    },
                },
            }
        }

        closed spec fn unit() -> Self {
            FractionalCarrier::Empty
        }

        proof fn closed_under_incl(a: Self, b: Self) {
        }

        proof fn commutative(a: Self, b: Self) {
        }

        proof fn associative(a: Self, b: Self, c: Self) {
        }

        proof fn op_unit(a: Self) {
        }

        proof fn unit_valid() {
        }
    }

    pub struct Frac<T, const TOTAL: u64 = 2> {
        r: Resource<FractionalCarrier<T, TOTAL>>,
    }

    impl<T, const TOTAL: u64> Frac<T, TOTAL> {
        #[verifier::type_invariant]
        pub closed spec fn inv(self) -> bool
        {
            self.r.value() is Value
        }

        pub closed spec fn id(self) -> Loc
        {
            self.r.loc()
        }

        pub closed spec fn view(self) -> T
        {
            self.r.value()->v
        }

        pub closed spec fn frac(self) -> int
        {
            self.r.value()->n
        }

        pub open spec fn valid(self, id: Loc, frac: int) -> bool
        {
            &&& self.id() == id
            &&& self.frac() == frac
        }

        pub proof fn dummy() -> (tracked result: Self)
            requires
                TOTAL > 0,
        {
            Self::new(arbitrary())
        }

        pub proof fn new(v: T) -> (tracked result: Self)
            requires
                TOTAL > 0,
            ensures
                result.frac() == TOTAL as int,
                result@ == v,
        {
            let f = FractionalCarrier::<T, TOTAL>::new(v);
            let tracked r = Resource::alloc(f);
            Frac { r }
        }

        pub proof fn agree(tracked self: &Self, tracked other: &Self)
            requires
                self.id() == other.id(),
            ensures
                self@ == other@,
        {
            use_type_invariant(self);
            use_type_invariant(other);
            let tracked joined = self.r.join_shared(&other.r);
            joined.validate()
        }

        pub proof fn take(tracked &mut self) -> (tracked result: Self)
            ensures
                result == *old(self),
        {
            self.bounded();
            let tracked mut mself = Self::dummy();
            tracked_swap(self, &mut mself);
            mself
        }

        pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
            requires
                0 < n < old(self).frac()
            ensures
                result.id() == self.id() == old(self).id(),
                self@ == old(self)@,
                result@ == old(self)@,
                self.frac() + result.frac() == old(self).frac(),
                result.frac() == n,
        {
            self.bounded();
            let tracked mut mself = Self::dummy();
            tracked_swap(self, &mut mself);
            use_type_invariant(&mself);
            let tracked (r1, r2) = mself.r.split(FractionalCarrier::Value { v: mself.r.value()->v,
                                                                            n: mself.r.value()->n - n },
                                                 FractionalCarrier::Value { v: mself.r.value()->v,
                                                                            n: n });
            self.r = r1;
            Self { r: r2 }
        }

        pub proof fn combine(tracked &mut self, tracked other: Self)
            requires
                old(self).id() == other.id(),
            ensures
                self.id() == old(self).id(),
                self@ == old(self)@,
                self@ == other@,
                self.frac() == old(self).frac() + other.frac(),
        {
            self.bounded();
            let tracked mut mself = Self::dummy();
            tracked_swap(self, &mut mself);
            use_type_invariant(&mself);
            use_type_invariant(&other);
            let tracked mut r = mself.r;
            r.validate_2(&other.r);
            *self = Self { r: r.join(other.r) };
        }

        pub proof fn update(tracked &mut self, v: T)
            requires
                old(self).frac() == TOTAL,
            ensures
                self.id() == old(self).id(),
                self@ == v,
                self.frac() == old(self).frac(),
        {
            self.bounded();
            let tracked mut mself = Self::dummy();
            tracked_swap(self, &mut mself);
            use_type_invariant(&mself);
            let tracked mut r = mself.r;
            let f = FractionalCarrier::<T, TOTAL>::Value { v: v, n: TOTAL as int };
            *self = Self { r: r.update(f) };
        }

        pub proof fn update_with(tracked &mut self, tracked other: &mut Self, v: T)
            requires
                old(self).id() == old(other).id(),
                old(self).frac() + old(other).frac() == TOTAL,
            ensures
                self.id() == old(self).id(),
                other.id() == old(other).id(),
                self.frac() == old(self).frac(),
                other.frac() == old(other).frac(),
                self@ == v,
                other@ == v,
        {
            let ghost other_frac = other.frac();
            other.bounded();

            let tracked mut xother = Self::dummy();
            tracked_swap(other, &mut xother);
            self.bounded();
            self.combine(xother);
            self.update(v);

            let tracked mut xother = self.split(other_frac);
            tracked_swap(other, &mut xother);
        }

        pub proof fn bounded(tracked &self)
            ensures
                0 < self.frac() <= TOTAL
        {
            use_type_invariant(self);
            self.r.validate()
        }
    }

    fn example_use()
    {
        let tracked mut r = Frac::<u64, 3>::new(123);
        assert(r@ == 123);
        assert(r.frac() == 3);
        let tracked r2 = r.split(2);
        assert(r@ == 123);
        assert(r2@ == 123);
        assert(r.frac() == 1);
        assert(r2.frac() == 2);
        proof {
            r.combine(r2);
            r.update(456);
        }
        assert(r@ == 456);
        assert(r.frac() == 3);

        let tracked mut a = Frac::<u32>::new(5);
        assert(a@ == 5);
        assert(a.frac() == 2);
        let tracked mut b = a.split(1);
        assert(a.frac() == 1);
        assert(b.frac() == 1);
        proof {
            a.update_with(&mut b, 123);
        }
        assert(a@ == 123);

        proof {
            a.combine(b);
            a.update(6);
        }
        assert(a@ == 6);
    }
}
