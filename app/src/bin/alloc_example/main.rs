use sl::allocator::*;
use sl::seq_view::*;

use std::collections::HashSet;

use vstd::prelude::*;

verus! {
    broadcast use vstd::std_specs::hash::group_hash_axioms;

    pub struct Pred {
        pub ghost id: int,
    }

    impl AllocatorPred<usize, SeqFrac<u8>> for Pred {
        open spec fn pred(self, k: usize, v: SeqFrac<u8>) -> bool {
            &&& v.valid(self.id)
            &&& v.off() == k
            &&& v@.len() == 1
        }

        proof fn exclusive(self, k: usize, tracked mut v1: SeqFrac<u8>, tracked v2: SeqFrac<u8>) {
            v1.disjoint(&v2);
        }
    }

    fn main() {
        let mut addrs = HashSet::<usize>::new();
        addrs.insert(0);
        addrs.insert(1);
        addrs.insert(2);

        let tracked (mut auth, mut frac) = SeqAuth::<u8>::new(seq![10, 11, 12]);
        let tracked f2 = frac.split(2);
        let tracked f1 = frac.split(1);
        let tracked f0 = frac;

        let tracked m = Map::<usize, SeqFrac<u8>>::tracked_empty();
        proof {
            m.tracked_insert(0, f0);
            m.tracked_insert(1, f1);
            m.tracked_insert(2, f2);
        }

        let tracked p = Pred {
            id: auth.id(),
        };

        let mut a = Allocator::<usize, _, Pred>::new(addrs, Tracked(m), Tracked(p));

        let r = a.alloc();
        match r {
            None => {
                assert(false);
            },
            Some((i, tv)) => {
                assert(p.pred(i, tv@));
                a.free(i, tv);
            },
        }
    }
}
