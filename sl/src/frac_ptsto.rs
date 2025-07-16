use vstd::prelude::*;
use vstd::raw_ptr::*;
use vstd::invariant::*;
use vstd::tokens::frac::*;

use std::sync::Arc;

verus! {
    enum Inner<T, const TOTAL: u64> {
        Present {
            tracked frac: FracGhost<T, TOTAL>,
            ptsto: PointsTo<T>,
        },
        Absent {
            tracked frac: FracGhost<T, TOTAL>,
        },
    }

    pub struct Pred {
        pub frac_id: int,
        pub ptsto_addr: usize,
    }

    impl<T, const TOTAL: u64> InvariantPredicate<Pred, Inner<T, TOTAL>> for Pred {
        closed spec fn inv(k: Pred, inner: Inner<T, TOTAL>) -> bool {
            match inner {
                Inner::Present { frac, ptsto } => {
                    &&& frac.valid(k.frac_id, 1)
                    &&& frac@ == ptsto.value()
                    &&& ptsto.ptr() as usize == k.ptsto_addr
                },
                Inner::Absent { frac } => {
                    &&& frac.valid(k.frac_id, TOTAL as int)
                },
            }
        }
    }

    struct Holder<T, const TOTAL: u64> {
        inv: Arc<AtomicInvariant<Pred, Inner<T, TOTAL>, Pred>>,
    }

    impl<T, const TOTAL: u64> Holder<T, TOTAL> {
        proof fn new(tracked ptsto: PointsTo<T>, ns: int) -> (tracked result: (Holder<T, TOTAL>, FracGhost<T, TOTAL>))
            requires
                TOTAL > 1,
                size_of::<T>() > 0,
            ensures
                result.0.inv(),
                result.0.namespace() == ns,
                result.0.ptsto_addr() == ptsto.ptr() as usize,
                result.1.valid(result.0.frac_id(), TOTAL-1),
        {
            let tracked mut frac = FracGhost::<T, TOTAL>::new(ptsto.value());
            let tracked frac_res = frac.split(TOTAL-1);
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
            &&& TOTAL > 1
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

        pub proof fn extract(tracked self, tracked mut f: FracGhost<T, TOTAL>, tracked credit: OpenInvariantCredit) -> (result: PointsTo<T>)
            requires
                self.inv(),
                f.valid(self.frac_id(), TOTAL-1),
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
                        inner = proof_from_false();
                    },
                };
            });
            result
        }

        pub proof fn deposit(tracked self, tracked ptsto: PointsTo<T>, tracked credit: OpenInvariantCredit) -> (result: FracGhost<T, TOTAL>)
            requires
                self.inv(),
                ptsto.ptr() as usize == self.ptsto_addr(),
            ensures
                result.valid(self.frac_id(), TOTAL-1),
                result@ == ptsto.value(),
            opens_invariants
                [ self.namespace() ]
        {
            let mut result;
            open_atomic_invariant_in_proof!(credit => &self.inv => inner => {
                match inner {
                    Inner::Present { frac, ptsto: other } => {
                        let tracked mut ptsto = ptsto;
                        ptsto.is_disjoint(&other);
                        inner = proof_from_false();
                    },
                    Inner::Absent { frac } => {
                        let tracked mut f = frac;
                        f.update(ptsto.value());
                        result = f.split(TOTAL-1);
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
