use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::invariant::*;

use crate::frac::*;

use std::sync::Arc;

verus! {
    enum Inner<T, const Total: u64> {
        Present {
            tracked frac: Frac<T, Total>,
            ptsto: PointsTo<T>,
        },
        Absent {
            tracked frac: Frac<T, Total>,
        },
    }

    struct Pred {
        pub frac_id: int,
        pub ptsto_addr: usize,
    }

    impl<T, const Total: u64> InvariantPredicate<Pred, Inner<T, Total>> for Pred {
        open spec fn inv(k: Pred, inner: Inner<T, Total>) -> bool {
            match inner {
                Inner::Present { frac, ptsto } => {
                    &&& frac.valid(k.frac_id, 1)
                    &&& frac@ == ptsto.value()
                    &&& ptsto.ptr() as usize == k.ptsto_addr
                },
                Inner::Absent { frac } => {
                    &&& frac.valid(k.frac_id, Total as int)
                },
            }
        }
    }

    struct Holder<T, const Total: u64> {
        inv: Arc<AtomicInvariant<Pred, Inner<T, Total>, Pred>>,
    }

    impl<T, const Total: u64> Holder<T, Total> {
        proof fn new(tracked ptsto: PointsTo<T>, ns: int) -> (tracked result: (Holder<T, Total>, Frac<T, Total>))
            requires
                Total > 1,
                size_of::<T>() > 0,
            ensures
                result.0.inv(),
                result.0.namespace() == ns,
                result.0.ptsto_addr() == ptsto.ptr() as usize,
                result.1.valid(result.0.frac_id(), Total-1),
        {
            let tracked mut frac = Frac::<T, Total>::new(ptsto.value());
            let tracked frac_res = frac.split(Total-1);
            let tracked inner = Inner::Present{ frac, ptsto };
            let pred = Pred{
                frac_id: frac.id(),
                ptsto_addr: ptsto.ptr() as usize,
            };
            let tracked inv = AtomicInvariant::<_, _, Pred>::new(pred, inner, ns);
            let tracked holder = Holder{
                inv: Arc::new(inv),
            };
            (holder, frac_res)
        }

        pub closed spec fn inv(self) -> bool {
            &&& Total > 1
            &&& size_of::<T>() > 0
        }

        pub closed spec fn frac_id(self) -> int {
            self.inv.constant().frac_id
        }

        pub closed spec fn ptsto_addr(self) -> usize {
            self.inv.constant().ptsto_addr
        }

        pub closed spec fn namespace(self) -> int {
            self.inv.namespace()
        }

        pub proof fn extract(tracked self, tracked mut f: Frac<T, Total>, tracked credit: OpenInvariantCredit) -> (result: PointsTo<T>)
            requires
                self.inv(),
                f.valid(self.frac_id(), Total-1),
            ensures
                result.ptr() as usize == self.ptsto_addr(),
            opens_invariants
                [ self.namespace() ]
        {
            let mut result;
            open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
                match inner {
                    Inner::Present { frac, ptsto } => {
                        result = ptsto;
                        f.combine(frac);
                        inner = Inner::Absent{ frac: f };
                    },
                    Inner::Absent { frac } => {
                        f.combine(frac);
                        f.bounded();
                        assert(false);
                        inner = Inner::Absent { frac: Frac::<T, Total>::dummy() };
                    },
                };
            });
            result
        }

        pub proof fn deposit(tracked self, tracked ptsto: PointsTo<T>, tracked credit: OpenInvariantCredit) -> (result: Frac<T, Total>)
            requires
                self.inv(),
                ptsto.ptr() as usize == self.ptsto_addr(),
            ensures
                result.valid(self.frac_id(), Total-1),
                result@ == ptsto.value(),
            opens_invariants
                [ self.namespace() ]
        {
            let mut result;
            open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
                match inner {
                    Inner::Present { frac, ptsto: other } => {
                        let mut ptsto = ptsto;
                        ptsto.is_disjoint(&other);
                        assert(false);
                        inner = Inner::Absent { frac: Frac::<T, Total>::dummy() };
                    },
                    Inner::Absent { frac } => {
                        let tracked mut f = frac;
                        f.update(ptsto.value());
                        result = f.split(Total-1);
                        inner = Inner::Present {
                            frac: f,
                            ptsto: ptsto,
                        };
                    },
                }
            });
            result
        }
    }
}
