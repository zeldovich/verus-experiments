use vstd::pcm::*;
use vstd::map::*;
use vstd::map_lib::*;
use vstd::prelude::*;
use vstd::modes::*;

// This implements a resource for ownership of keys in a map.

verus! {
    #[verifier::reject_recursive_types(K)]
    #[verifier::ext_equal]
    struct MapView<K, V> {
        auth: Option<Option<Map<K, V>>>,
        frac: Option<Map<K, V>>,
    }

    impl<K, V> PCM for MapView<K, V> {
        closed spec fn valid(self) -> bool {
            match self.frac {
                None => false,
                Some(f) => match self.auth {
                    None => true,
                    Some(None) => false,
                    Some(Some(a)) => f.submap_of(a),
                }
            }
        }

        closed spec fn op(self, other: Self) -> Self {
            MapView {
                auth: if self.auth.is_Some() { if other.auth.is_Some() { Some(None) } else { self.auth } } else { other.auth },
                frac: match self.frac {
                    None => None,
                    Some(sfr) => match other.frac {
                        None => None,
                        Some(ofr) => {
                            if sfr.dom().disjoint(ofr.dom()) {
                                Some(sfr.union_prefer_right(ofr))
                            } else {
                                None
                            }
                        },
                    },
                },
            }
        }

        closed spec fn unit() -> Self {
            MapView {
                auth: None,
                frac: Some(Map::empty()),
            }
        }

        proof fn closed_under_incl(a: Self, b: Self) {
            broadcast use lemma_submap_of_trans;
            broadcast use lemma_op_frac_submap_of;
        }

        proof fn commutative(a: Self, b: Self) {
            let ab = Self::op(a, b);
            let ba = Self::op(b, a);
            assert(ab == ba);
        }

        proof fn associative(a: Self, b: Self, c: Self) {
            let bc = Self::op(b, c);
            let ab = Self::op(a, b);
            let a_bc = Self::op(a, bc);
            let ab_c = Self::op(ab, c);
            assert(a_bc == ab_c);
        }

        proof fn op_unit(a: Self) {
            let x = Self::op(a, Self::unit());
            assert(a == x);
        }

        proof fn unit_valid() {
        }
    }

    broadcast proof fn lemma_op_frac_submap_of<K, V>(a: MapView<K, V>, b: MapView<K, V>)
        requires
            #[trigger] MapView::op(a, b).valid(),
        ensures
            a.frac.unwrap() <= MapView::op(a, b).frac.unwrap(),
            b.frac.unwrap() <= MapView::op(a, b).frac.unwrap(),
    {
    }

    #[verifier::reject_recursive_types(K)]
    pub struct MapAuth<K, V> {
        r: Resource<MapView<K, V>>,
    }

    #[verifier::reject_recursive_types(K)]
    pub struct MapFrac<K, V> {
        r: Resource<MapView<K, V>>,
    }

    impl<K, V> MapAuth<K, V> {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.r.value().auth.is_Some()
            &&& self.r.value().auth.unwrap().is_Some()
            &&& self.r.value().frac == Some(Map::<K, V>::empty())
        }

        pub closed spec fn id(self) -> Loc
        {
            self.r.loc()
        }

        pub open spec fn valid(self, id: Loc) -> bool
        {
            &&& self.inv()
            &&& self.id() == id
        }

        pub closed spec fn view(self) -> Map<K, V>
        {
            self.r.value().auth.unwrap().unwrap()
        }

        pub proof fn dummy() -> (tracked result: MapAuth<K, V>)
        {
            let tracked r = Resource::alloc(MapView::unit());
            MapAuth{ r }
        }

        pub proof fn take(tracked &mut self) -> (tracked result: MapAuth<K, V>)
            requires
                old(self).inv(),
            ensures
                result == *old(self),
        {
            let tracked mut r = Self::dummy();
            tracked_swap(self, &mut r);
            r
        }

        pub proof fn empty(tracked &self) -> (tracked result: MapFrac<K, V>)
            requires
                self.inv(),
            ensures
                result.valid(self.id()),
                result@ == Map::<K, V>::empty(),
        {
            MapFrac::<K, V>::empty(self.id())
        }

        pub proof fn insert(tracked &mut self, m: Map<K, V>) -> (tracked result: MapFrac<K, V>)
            requires
                old(self).inv(),
                old(self)@.dom().disjoint(m.dom()),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ == old(self)@.union_prefer_right(m),
                result.inv(),
                result.id() == self.id(),
                result@ == m,
        {
            broadcast use lemma_submap_of_trans;
            broadcast use lemma_op_frac_submap_of;

            let tracked mut r = Resource::alloc(MapView::<K, V>::unit());
            tracked_swap(&mut self.r, &mut r);

            let rr = MapView {
                auth: Some(Some(r.value().auth.unwrap().unwrap().union_prefer_right(m))),
                frac: Some(m),
            };

            let tracked r_upd = r.update(rr);

            let arr = MapView {
                auth: r_upd.value().auth,
                frac: Some(Map::empty()),
            };

            let frr = MapView {
                auth: None,
                frac: r_upd.value().frac,
            };

            assert(r_upd.value() == MapView::op(arr, frr));
            let tracked (ar, fr) = r_upd.split(arr, frr);
            self.r = ar;
            MapFrac { r: fr }
        }

        pub proof fn delete(tracked &mut self, tracked f: MapFrac<K, V>)
            requires
                old(self).inv(),
                f.valid(old(self).id()),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ == old(self)@.remove_keys(f@.dom()),
        {
            broadcast use lemma_submap_of_trans;
            broadcast use lemma_op_frac_submap_of;

            let tracked mut r = Resource::alloc(MapView::<K, V>::unit());
            tracked_swap(&mut self.r, &mut r);

            r = r.join(f.r);

            let ra = r.value().auth.unwrap().unwrap();
            let ra_new = ra.remove_keys(f@.dom());

            let rnew = MapView {
                auth: Some(Some(ra_new)),
                frac: Some(Map::empty()),
            };

            self.r = r.update(rnew);
        }

        pub proof fn new(m: Map<K, V>) -> (tracked result: (MapAuth<K, V>, MapFrac<K, V>))
            ensures
                result.0.inv(),
                result.1.inv(),
                result.0.id() == result.1.id(),
                result.0@ == m,
                result.1@ == m,
        {
            let tracked rr = Resource::alloc(MapView{
                auth: Some(Some(m)),
                frac: Some(m),
            });

            let arr = MapView{
                auth: Some(Some(m)),
                frac: Some(Map::empty()),
            };

            let frr = MapView{
                auth: None,
                frac: Some(m),
            };

            assert(rr.value() == MapView::op(arr, frr));
            let tracked (ar, fr) = rr.split(arr, frr);
            (MapAuth { r: ar }, MapFrac { r: fr })
        }
    }

    impl<K, V> MapFrac<K, V> {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.r.value().auth.is_None()
            &&& self.r.value().frac.is_Some()
        }

        pub closed spec fn id(self) -> Loc
        {
            self.r.loc()
        }

        pub closed spec fn view(self) -> Map<K, V>
        {
            self.r.value().frac.unwrap()
        }

        pub open spec fn valid(self, id: Loc) -> bool
        {
            &&& self.inv()
            &&& self.id() == id
        }

        pub proof fn dummy() -> (tracked result: MapFrac<K, V>)
        {
            let tracked r = Resource::alloc(MapView::unit());
            MapFrac{ r }
        }

        pub proof fn empty(id: int) -> (tracked result: MapFrac<K, V>)
            ensures
                result.valid(id),
                result@ == Map::<K, V>::empty(),
        {
            let tracked r = Resource::create_unit(id);
            MapFrac{ r }
        }

        pub proof fn take(tracked &mut self) -> (tracked result: MapFrac<K, V>)
            requires
                old(self).inv(),
            ensures
                result == *old(self),
        {
            let tracked mut r = Self::dummy();
            tracked_swap(self, &mut r);
            r
        }

        pub proof fn agree(tracked self: &MapFrac<K, V>, tracked auth: &MapAuth<K, V>)
            requires
                self.inv(),
                auth.inv(),
                self.id() == auth.id(),
            ensures
                self@ <= auth@
        {
            broadcast use lemma_submap_of_trans;

            let tracked joined = self.r.join_shared(&auth.r);
            joined.validate();
            assert(self.r.value().frac.unwrap() <= joined.value().frac.unwrap());
        }

        pub proof fn combine(tracked &mut self, tracked other: MapFrac<K, V>)
            requires
                old(self).inv(),
                other.inv(),
                old(self).id() == other.id(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ == old(self)@.union_prefer_right(other@),
                old(self)@.dom().disjoint(other@.dom()),
        {
            let tracked mut r = Resource::alloc(MapView::unit());
            tracked_swap(&mut self.r, &mut r);
            r.validate_2(&other.r);
            self.r = r.join(other.r);
        }

        pub proof fn disjoint(tracked &mut self, tracked other: &MapFrac<K, V>)
            requires
                old(self).inv(),
                other.inv(),
                old(self).id() == other.id(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ == old(self)@,
                self@.dom().disjoint(other@.dom()),
        {
            self.r.validate_2(&other.r);
        }

        pub proof fn split(tracked &mut self, s: Set<K>) -> (tracked result: MapFrac<K, V>)
            requires
                old(self).inv(),
                s <= old(self)@.dom(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                result.inv(),
                result.id() == self.id(),
                old(self)@ == self@.union_prefer_right(result@),
                result@.dom() =~= s,
                self@.dom() =~= old(self)@.dom() - s,
        {
            let tracked mut r = Resource::alloc(MapView::<K, V>::unit());
            tracked_swap(&mut self.r, &mut r);

            let rr1 = MapView {
                auth: None,
                frac: Some(r.value().frac.unwrap().remove_keys(s)),
            };

            let rr2 = MapView {
                auth: None,
                frac: Some(r.value().frac.unwrap().restrict(s)),
            };

            assert(r.value().frac == MapView::op(rr1, rr2).frac);
            let tracked (r1, r2) = r.split(rr1, rr2);
            self.r = r1;
            MapFrac{ r: r2 }
        }

        pub proof fn update(tracked &mut self, tracked auth: &mut MapAuth<K, V>, m: Map<K, V>)
            requires
                old(self).inv(),
                old(auth).inv(),
                m.dom() <= old(self)@.dom(),
                old(self).id() == old(auth).id(),
            ensures
                self.inv(),
                auth.inv(),
                self.id() == old(self).id(),
                auth.id() == old(auth).id(),
                self@ == old(self)@.union_prefer_right(m),
                auth@ == old(auth)@.union_prefer_right(m),
        {
            broadcast use lemma_submap_of_trans;
            broadcast use lemma_op_frac_submap_of;

            let tracked mut fr = Resource::alloc(MapView::<K, V>::unit());
            tracked_swap(&mut self.r, &mut fr);

            let tracked mut ar = Resource::alloc(MapView::<K, V>::unit());
            tracked_swap(&mut auth.r, &mut ar);

            fr.validate_2(&ar);
            let tracked mut r = fr.join(ar);

            assert(r.value().frac == fr.value().frac);

            let rr = MapView {
                auth: Some(Some(r.value().auth.unwrap().unwrap().union_prefer_right(m))),
                frac: Some(r.value().frac.unwrap().union_prefer_right(m)),
            };

            let tracked r_upd = r.update(rr);

            let arr = MapView {
                auth: r_upd.value().auth,
                frac: Some(Map::empty()),
            };

            let frr = MapView {
                auth: None,
                frac: r_upd.value().frac,
            };

            assert(r_upd.value().frac == MapView::op(arr, frr).frac);
            let tracked (ar, fr) = r_upd.split(arr, frr);
            auth.r = ar;
            self.r = fr;
        }
    }
}
