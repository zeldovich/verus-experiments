use vstd::pcm::*;
use vstd::prelude::*;
use vstd::modes::*;

// This implements a resource for owning a prefix of a seq, with a designated
// prefix owner.  The allowed operations are:
//
// - appending to the authoritative resource (without needing the prefix resource)
// - agreeing that the prefix resource is a prefix of the authoritative resource
// - advancing the prefix resource to the authoritative resource
// - truncating some prefix of the prefix resource and authoritative resource

verus! {
    enum SeqPrefixView<V> {
        Valid(Option<Seq<V>>, Option<Seq<V>>),
        Invalid,
    }

    impl<V> PCM for SeqPrefixView<V> {
        closed spec fn valid(self) -> bool {
            match self {
                Self::Invalid => false,
                Self::Valid(Some(a), Some(f)) => f.is_prefix_of(a),
                _ => true,
            }
        }

        closed spec fn op(self, other: Self) -> Self {
            match (self, other) {
                (Self::Invalid, _) => Self::Invalid,
                (_, Self::Invalid) => Self::Invalid,
                (Self::Valid(Some(_), _), Self::Valid(Some(_), _)) => Self::Invalid,
                (Self::Valid(_, Some(_)), Self::Valid(_, Some(_))) => Self::Invalid,
                (Self::Valid(a, None), Self::Valid(None, f)) => Self::Valid(a, f),
                (Self::Valid(a, f), Self::Valid(None, None)) => Self::Valid(a, f),
                (Self::Valid(None, None), Self::Valid(a, f)) => Self::Valid(a, f),
                (Self::Valid(None, f), Self::Valid(a, None)) => Self::Valid(a, f),
            }
        }

        closed spec fn unit() -> Self {
            Self::Valid(None, None)
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

    pub struct SeqPrefixAuth<V> {
        r: Resource<SeqPrefixView<V>>,
    }

    pub struct SeqPrefix<V> {
        r: Resource<SeqPrefixView<V>>,
    }

    impl<V> SeqPrefixAuth<V> {
        pub closed spec fn inv(self) -> bool {
            match self.r.value() {
                SeqPrefixView::Valid(Some(_), None) => true,
                _ => false,
            }
        }

        pub closed spec fn id(self) -> int {
            self.r.loc()
        }

        pub closed spec fn view(self) -> Seq<V> {
            match self.r.value() {
                SeqPrefixView::Valid(Some(a), None) => a,
                _ => Seq::empty(),
            }
        }

        pub proof fn new(s: Seq<V>) -> (tracked result: (SeqPrefixAuth<V>, SeqPrefix<V>))
            ensures
                result.0.id() == result.1.id(),
                result.0@ == s,
                result.1@ == s,
        {
            let tracked rr = Resource::alloc(SeqPrefixView::Valid(Some(s), Some(s)));
            let arr = SeqPrefixView::Valid(Some(s), None);
            let frr = SeqPrefixView::Valid(None, Some(s));
            let tracked (ar, fr) = rr.split(arr, frr);
            (SeqPrefixAuth{ r: ar }, SeqPrefix{ r: fr })
        }

        pub proof fn push(tracked &mut self, v: V)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ == old(self)@.push(v),
        {
            let selfv = self@;
            let tracked mut r = Resource::alloc(SeqPrefixView::unit());
            tracked_swap(&mut self.r, &mut r);
            let rr = SeqPrefixView::Valid(Some(selfv.push(v)), None);
            r = r.update(rr);
            self.r = r;
        }

        pub proof fn append(tracked &mut self, vs: Seq<V>)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self@ == old(self)@ + vs,
        {
            let selfv = self@;
            let tracked mut r = Resource::alloc(SeqPrefixView::unit());
            tracked_swap(&mut self.r, &mut r);
            let rr = SeqPrefixView::Valid(Some(selfv + vs), None);
            r = r.update(rr);
            self.r = r;
        }

        pub proof fn agree(tracked &self, tracked prefix: &SeqPrefix<V>)
            requires
                self.inv(),
                prefix.inv(),
                self.id() == prefix.id(),
            ensures
                prefix@.is_prefix_of(self@),
        {
            let tracked joined = self.r.join_shared(&prefix.r);
            joined.validate()
        }

        pub proof fn truncate(tracked &mut self, tracked prefix: &mut SeqPrefix<V>, n: int)
            requires
                old(self).inv(),
                old(prefix).inv(),
                old(self).id() == old(prefix).id(),
                0 <= n <= old(prefix)@.len(),
            ensures
                self.inv(),
                prefix.inv(),
                self.id() == old(self).id(),
                prefix.id() == old(prefix).id(),
                self@ == old(self)@.subrange(n, old(self)@.len() as int),
                prefix@ == old(prefix)@.subrange(n, old(prefix)@.len() as int),
        {
            self.agree(prefix);

            let selfv = self@;
            let tracked mut sr = Resource::alloc(SeqPrefixView::unit());
            tracked_swap(&mut self.r, &mut sr);

            let prefixv = prefix@;
            let tracked mut pr = Resource::alloc(SeqPrefixView::unit());
            tracked_swap(&mut prefix.r, &mut pr);

            let tracked mut r = sr.join(pr);
            r = r.update(SeqPrefixView::Valid(Some(selfv.subrange(n, selfv.len() as int)),
                                              Some(prefixv.subrange(n, prefixv.len() as int))));
            let tracked (sr, pr) = r.split(
                SeqPrefixView::Valid(Some(selfv.subrange(n, selfv.len() as int)), None),
                SeqPrefixView::Valid(None, Some(prefixv.subrange(n, prefixv.len() as int))));

            self.r = sr;
            prefix.r = pr;
        }

        pub proof fn advance(tracked &mut self, tracked prefix: &mut SeqPrefix<V>, n: int)
            requires
                old(self).inv(),
                old(prefix).inv(),
                old(self).id() == old(prefix).id(),
                old(prefix)@.len() <= n <= old(self)@.len(),
            ensures
                self.inv(),
                prefix.inv(),
                self.id() == old(self).id(),
                prefix.id() == old(prefix).id(),
                self@ == old(self)@,
                old(prefix)@.is_prefix_of(old(self)@),
                prefix@ == old(self)@.subrange(0, n),
        {
            self.agree(prefix);

            let selfv = self@;
            let tracked mut sr = Resource::alloc(SeqPrefixView::unit());
            tracked_swap(&mut self.r, &mut sr);

            let prefixv = prefix@;
            let tracked mut pr = Resource::alloc(SeqPrefixView::unit());
            tracked_swap(&mut prefix.r, &mut pr);

            let tracked mut r = sr.join(pr);
            r = r.update(SeqPrefixView::Valid(Some(selfv),
                                              Some(selfv.subrange(0, n))));
            let tracked (sr, pr) = r.split(
                SeqPrefixView::Valid(Some(selfv), None),
                SeqPrefixView::Valid(None, Some(selfv.subrange(0, n))));

            self.r = sr;
            prefix.r = pr;
        }
    }

    impl<V> SeqPrefix<V> {
        pub closed spec fn inv(self) -> bool {
            match self.r.value() {
                SeqPrefixView::Valid(None, Some(_)) => true,
                _ => false,
            }
        }

        pub closed spec fn id(self) -> int {
            self.r.loc()
        }

        pub closed spec fn view(self) -> Seq<V> {
            match self.r.value() {
                SeqPrefixView::Valid(None, Some(f)) => f,
                _ => Seq::empty(),
            }
        }
    }
}
