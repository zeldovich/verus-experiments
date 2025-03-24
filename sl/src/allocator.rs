use std::collections::HashSet;

use vstd::prelude::*;
use vstd::std_specs::hash::IterAdditionalSpecFns;

verus! {
    broadcast use vstd::std_specs::hash::group_hash_axioms;

    pub trait AllocatorPred<K, T> : Sized {
        spec fn pred(self, k: K, t: T) -> bool;

        proof fn exclusive(self, k: K, tracked t1: T, tracked t2: T)
            requires
                self.pred(k, t1),
                self.pred(k, t2),
            ensures
                false;
    }

    #[verifier::reject_recursive_types(K)]
    pub struct Allocator<K, T, Pred: AllocatorPred<K, T>> {
        pub s: HashSet<K>,
        pub r: Tracked<Map<K, T>>,
        pub p: Tracked<Pred>,
    }

    impl<K, T, Pred> Allocator<K, T, Pred>
        where
            Pred: AllocatorPred<K, T>,
            K: Copy,
            K: std::cmp::Eq,
            K: std::hash::Hash,
    {
        pub open spec fn inv(self) -> bool {
            &&& vstd::std_specs::hash::obeys_key_model::<K>()
            &&& self.s@ == self.r@.dom()
            &&& forall |k| #[trigger] self.r@.contains_key(k) ==> self.p@.pred(k, self.r@[k])
        }

        pub open spec fn pred(self) -> Pred {
            self.p@
        }

        pub open spec fn view(self) -> Set<K> {
            self.s@
        }

        pub fn new(s: HashSet<K>, Tracked(r): Tracked<Map<K, T>>, Tracked(p): Tracked<Pred>) -> (result: Self)
            requires
                s@ == r.dom(),
                forall |k| #[trigger] r.contains_key(k) ==> p.pred(k, r[k]),
                vstd::std_specs::hash::obeys_key_model::<K>(),
            ensures
                result.inv(),
                result.pred() == p,
                result@ == s@,
        {
            Self{
                s: s,
                r: Tracked(r),
                p: Tracked(p),
            }
        }

        pub fn alloc(&mut self) -> (result: Option<(K, Tracked<T>)>)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self.pred() == old(self).pred(),
                match result {
                    None => {
                        &&& self@ == old(self)@
                        &&& self.s@.len() == 0
                    }
                    Some(r) => {
                        &&& self@ == old(self)@.remove(r.0)
                        &&& self.pred().pred(r.0, r.1@)
                    }
                },
        {
            let mut i = self.s.iter();
            let e = i.next();
            match e {
                None => {
                    assert(i@.1.to_set() == Set::<K>::empty());
                    None
                }
                Some(kp) => {
                    let k = *kp;
                    self.s.remove(&k);
                    let tracked t = self.r.borrow_mut().tracked_remove(k);
                    assert(self.p@.pred(k, t));
                    Some((k, Tracked(t)))
                }
            }
        }

        pub fn free(&mut self, k: K, Tracked(v): Tracked<T>)
            requires
                old(self).inv(),
                old(self).pred().pred(k, v)
            ensures
                self.inv(),
                self.pred() == old(self).pred(),
                self@ == old(self)@.insert(k),
        {
            proof {
                if self.s@.contains(k) {
                    let tracked t = self.r.borrow_mut().tracked_remove(k);
                    self.pred().exclusive(k, v, t);
                } else {
                    self.r.borrow_mut().tracked_insert(k, v);
                }
            }
            self.s.insert(k);
        }
    }
}
