use builtin::*;
use vstd::pcm::*;
use vstd::prelude::*;
use vstd::modes::*;

// This implements a resource for fractional ownership of a ghost variable.
// The fractions are represented as some number out of a compile-time const
// Total value; you can have any fractions from 1 up to Total, and if you
// have Total, you can update the ghost variable.

verus! {
    // Too bad that `nat` and `int` are forbidden as the type of a const generic parameter
    enum FractionalCarrier<T, const Total: u64> {
        Value { v: T, n: int },
        Empty,
        Invalid,
    }

    impl<T, const Total: u64> FractionalCarrier<T, Total> {
        spec fn new(v: T) -> Self {
            FractionalCarrier::Value { v: v, n: Total as int }
        }
    }

    impl<T, const Total: u64> PCM for FractionalCarrier<T, Total> {
        closed spec fn valid(self) -> bool {
            match self {
                FractionalCarrier::Invalid => false,
                FractionalCarrier::Empty => true,
                FractionalCarrier::Value { v: v, n: n } => 0 < n <= Total,
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

    pub struct Frac<T, const Total: u64 = 2> {
        r: Resource<FractionalCarrier<T, Total>>,
    }

    impl<T, const Total: u64> Frac<T, Total> {
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
            &&& self.inv()
            &&& self.id() == id
            &&& self.frac() == frac
        }

        pub proof fn dummy() -> (tracked result: Self)
        {
            let tracked r = Resource::alloc(FractionalCarrier::unit());
            Frac{ r }
        }

        pub proof fn new(v: T) -> (tracked result: Self)
            requires
                Total > 0,
            ensures
                result.inv(),
                result.frac() == Total as int,
                result@ == v,
        {
            let f = FractionalCarrier::<T, Total>::new(v);
            let tracked r = Resource::alloc(f);
            Frac { r }
        }

        pub proof fn agree(tracked self: &Self, tracked other: &Self)
            requires
                self.inv(),
                other.inv(),
                self.id() == other.id(),
            ensures
                self@ == other@,
        {
            let tracked joined = self.r.join_shared(&other.r);
            joined.validate()
        }

        pub proof fn take(tracked &mut self) -> (tracked result: Self)
            requires
                old(self).inv(),
            ensures
                result == *old(self),
        {
            let tracked mut r = Self::dummy();
            tracked_swap(self, &mut r);
            r
        }

        pub proof fn split(tracked &mut self, n: int) -> (tracked result: Self)
            requires
                old(self).inv(),
                0 < n < old(self).frac()
            ensures
                result.id() == self.id() == old(self).id(),
                self.inv(),
                result.inv(),
                self@ == old(self)@,
                result@ == old(self)@,
                self.frac() + result.frac() == old(self).frac(),
                result.frac() == n,
        {
            let tracked mut r = Resource::alloc(FractionalCarrier::unit());
            tracked_swap(&mut self.r, &mut r);
            let tracked (r1, r2) = r.split(FractionalCarrier::Value { v: r.value()->v,
                                                                      n: r.value()->n - n },
                                           FractionalCarrier::Value { v: r.value()->v,
                                                                      n: n });
            self.r = r1;
            Self { r: r2 }
        }

        pub proof fn combine(tracked &mut self, tracked other: Self)
            requires
                old(self).inv(),
                other.inv(),
                old(self).id() == other.id(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ == old(self)@,
                self@ == other@,
                self.frac() == old(self).frac() + other.frac(),
        {
            let tracked mut r = Resource::alloc(FractionalCarrier::unit());
            tracked_swap(&mut self.r, &mut r);
            r.validate_2(&other.r);
            self.r = r.join(other.r);
        }

        pub proof fn update(tracked &mut self, v: T)
            requires
                old(self).inv(),
                old(self).frac() == Total,
            ensures
                self.id() == old(self).id(),
                self.inv(),
                self@ == v,
                self.frac() == old(self).frac(),
        {
            let tracked mut r = Resource::alloc(FractionalCarrier::unit());
            tracked_swap(&mut self.r, &mut r);
            let f = FractionalCarrier::<T, Total>::Value { v: v, n: Total as int };
            self.r = r.update(f);
        }

        pub proof fn bounded(tracked &self)
            requires
                self.inv(),
            ensures
                0 < self.frac() <= Total
        {
            self.r.validate()
        }
    }

    fn main()
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
        let tracked b = a.split(1);
        assert(a.frac() == 1);
        assert(b.frac() == 1);
        proof {
            a.combine(b);
            a.update(6);
        }
        assert(a@ == 6);
    }
}
