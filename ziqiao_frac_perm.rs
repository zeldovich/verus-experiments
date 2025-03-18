/// A fully verified frac-based ownership to share tracked ghost permissions.
/// This is motivated by PCM from vstd and https://github.com/zeldovich/verus-experiments/blob/main/disk/frac.rs
/// The state-machine proofs are motivated from the proof for Rc in vstd.

use state_machines_macros::*;
use vstd::multiset::*;
use vstd::prelude::*;

verus! {

pub trait SumTrait {
    spec fn count(&self) -> nat;
}

pub open spec fn sum<T: SumTrait>(s: Multiset<T>) -> nat
    decreases s.len(),
{
    if s.len() > 0 {
        let e = s.choose();
        e.count() + sum(s.remove(e))
    } else {
        0
    }
}

proof fn lemma_sum_insert<T: SumTrait>(s: Multiset<T>, elem: T)
    ensures
        sum(s) + elem.count() == sum(s.insert(elem)),
{
    assert(s.insert(elem).remove(elem) =~= s);
    lemma_sum(s.insert(elem), elem);
}

proof fn lemma_sum<T: SumTrait>(s: Multiset<T>, elem: T)
    requires
        s.contains(elem),
    ensures
        sum(s.remove(elem)) + elem.count() == sum(s),
    decreases s.len(),
{
    let news = s.remove(elem);
    let e = s.choose();
    if s.len() > 1 {
        if e != elem {
            lemma_sum(s.remove(e), elem);
            lemma_sum(s.remove(elem), e);
            assert(s.remove(elem).remove(e) =~= s.remove(e).remove(elem));
        }
    } else {
        Multiset::lemma_is_singleton(s);
        assert(s.contains(e));
    }
}

impl SumTrait for nat {
    open spec fn count(&self) -> nat {
        *self
    }
}

} // verus!

tokenized_state_machine!(RefCounter<Perm> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<Perm>,

        #[sharding(constant)]
        pub val: Perm,

        #[sharding(multiset)]
        pub reader: Multiset<Perm>,

        #[sharding(constant)]
        pub total: nat,     // Maximum number of shares

        #[sharding(multiset)]
        pub frac: Multiset<nat>, // assigned shares and must sum up to total.
    }

    #[invariant]
    pub fn frac_agrees_non_zero(&self) -> bool {
        forall |s| #[trigger]self.frac.contains(s) ==> s > 0
    }

    #[invariant]
    pub fn frac_agrees_total(&self) -> bool {
        ( self.frac.len() > 0 ==> sum(self.frac) == self.total )
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        (self.storage.is_some() ==> self.storage == Some(self.val))
    }

    #[invariant]
    pub fn reader_agrees_counters(&self) -> bool {
        self.frac.len() == self.reader.count(self.val)
    }

    #[invariant]
    pub fn counter_agrees_storage(&self) -> bool {
        self.reader.count(self.val) > 0 ==> self.storage == Some(self.val)
    }

    #[invariant]
    pub fn counter_agrees_empty_storage(&self) -> bool {
        self.frac.len() == 0 ==> self.storage.is_none()
    }

    init!{
        initialize_once(x: Perm, total: nat) {
            require total > 0;
            init storage = Option::Some(x);
            init reader = Multiset::empty().insert(x);
            init val = x;
            init total = total;
            init frac = Multiset::empty().insert(total);
        }
    }

    #[inductive(initialize_once)]
    fn initialize_once_inductive(post: Self, x: Perm, total: nat) {
        let frac = Multiset::<nat>::empty().insert(total);
        lemma_sum(frac, total);
        assert(sum(frac) == total);
    }

    property! {
        reader_guard() {
            have reader >= {pre.val};
            guard storage >= Some(pre.val);
        }
    }

    transition! {
        do_share(shares: nat, new_shares: nat) {
            have reader >= {pre.val};
            require(0 < new_shares < shares);
            add reader += {pre.val};
            remove frac -= {shares};
            add frac += {new_shares};
            add frac += {(shares - new_shares) as nat};
        }
    }

    transition! {
        take() {
            remove reader -= {pre.val};
            remove frac -= {pre.total};
            withdraw storage -= Some(pre.val);
        }
    }

    #[inductive(take)]
    fn take_inductive(pre: Self, post: Self) {
        assert(pre.reader.count(pre.val) > 0);
        assert(pre.frac.count(pre.total) > 0);
        lemma_sum(pre.frac, pre.total);
        let frac1 = pre.frac.remove(pre.total);
        if pre.frac.len() > 1 {
            let e = frac1.choose();
            assert(frac1.contains(e));
            lemma_sum(frac1, e);
        }
        assert forall |s| #[trigger]post.frac.contains(s)
        implies s > 0 by{
            assert(pre.frac.contains(s));
        }
    }

    #[inductive(do_share)]
    fn do_share_inductive(pre: Self, post: Self, shares: nat, new_shares: nat) {
        assert(pre.frac.count(shares) > 0);
        assert(pre.reader.count(pre.val) > 0);
        assert(pre.storage == Option::Some(pre.val));
        assert(pre.storage.is_Some());
        let frac1 = pre.frac.remove(shares);
        let frac2 = frac1.insert(new_shares);
        lemma_sum(pre.frac, shares);
        lemma_sum_insert(frac1, new_shares);
        lemma_sum_insert(frac2, (shares - new_shares) as nat);
        assert forall |s| #[trigger]post.frac.contains(s)
        implies s > 0 by{
            assert(pre.frac.contains(s) || s == new_shares || s == (shares - new_shares) as nat);
        }
    }

    transition!{
        merge(shares1: nat, shares2: nat) {
            let new_shares = (shares1 + shares2) as nat;
            remove reader -= {pre.val};
            remove reader -= {pre.val};
            remove frac -= {shares1};
            remove frac -= {shares2};
            add reader += {pre.val};
            add frac += {new_shares};
        }
    }


    #[inductive(merge)]
    fn merge_inductive(pre: Self, post: Self, shares1: nat, shares2: nat) {
        let x = pre.val;
        let new_shares = (shares1 + shares2) as nat;
        assert(pre.reader.count(x) > 0);
        assert(pre.storage == Option::Some(x));
        assert(pre.frac.contains(shares1));
        assert(pre.frac.contains(shares2));
        assert(shares1 + shares2 > 0);
        let frac1 = pre.frac.remove(shares1);
        let frac2 = frac1.remove(shares2);
        lemma_sum(pre.frac, shares1);
        lemma_sum(frac1, shares2);
        lemma_sum_insert(frac2, (shares1 + shares2) as nat);
        assert forall |s| #[trigger]post.frac.contains(s)
        implies s > 0 by{
            assert(pre.frac.contains(s) || s == (shares1 + shares2) as nat);
        };
    }
});

#[cfg(verus_keep_ghost)]
verus! {

struct_with_invariants!{
/// A `tracked ghost` container that you can put a ghost object in.
/// A `Shared<T>` is duplicable and lets you get a `&T` out.
pub tracked struct FracPerm<T> {
    tracked inst: RefCounter::Instance<T>,
    tracked reader: RefCounter::reader<T>,
    tracked frac: RefCounter::frac<T>,
    ghost shares: nat,
    ghost total: nat,
}
spec fn wf(self) -> bool {
    predicate {
        &&& self.reader.instance_id() == self.inst.id()
        &&& self.reader.element() == self.inst.val()
        &&& self.total >= self.shares > 0
        &&& self.total == self.inst.total()
        &&& self.frac.element() == self.shares
        &&& self.frac.instance_id() ==self.inst.id()
    }
}
}

impl<T> FracPerm<T> {
    pub closed spec fn id(self) -> InstanceId {
        self.inst.id()
    }

    pub closed spec fn view(self) -> T {
        self.inst.val()
    }

    pub closed spec fn shares(&self) -> nat {
        self.shares
    }

    pub closed spec fn total(&self) -> nat {
        self.total
    }

    pub closed spec fn well_formed(&self) -> bool {
        self.wf()
    }

    pub proof fn new(tracked t: T, total: nat) -> (tracked s: Self)
        requires
            total > 0,
        ensures
            s@ == t,
    {
        let tracked (Tracked(inst), Tracked(mut readers), Tracked(mut fracs)) =
            RefCounter::Instance::initialize_once(t, total, Some(t));
        let tracked reader = readers.remove(t);
        let tracked frac = fracs.remove(total);
        let shares = total;
        FracPerm { inst, reader, frac, shares, total }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        requires
            self.well_formed(),
        ensures
            *t == self@,
    {
        self.inst.reader_guard(&self.reader)
    }

    pub proof fn share(tracked self, n: nat) -> (tracked ret: (
        Self,
        Self,
    ))
        requires
            self.well_formed(),
            0 < n < self.shares(),
        ensures
            ret.0.well_formed(),
            ret.1.well_formed(),
            self@ == ret.0@,
            self@ == ret.1@,
            self.id() == ret.0.id(),
            self.id() == ret.1.id(),
            ret.0.shares() + ret.1.shares() == self.shares(),
    {
        let tracked FracPerm { mut inst, mut reader, mut frac, mut shares, total } = self;
        let tracked mut reader1;
        let tracked mut reader2;
        let tracked mut frac1;
        let tracked mut frac2;
            let tracked (Tracked(r), Tracked(f1), Tracked(f2)) = inst.do_share(shares, n, &reader, frac);
            reader1 = reader;
            reader2 = r;
            frac1 = f1;
            frac2 = f2;
        let tracked left = FracPerm {
            inst,
            reader: reader1,
            frac: frac1,
            shares: n,
            total,
        };
        let tracked right = FracPerm {
            inst,
            reader: reader2,
            frac: frac2,
            shares: (shares - n) as nat,
            total,
        };
        (left, right)
    }

    pub proof fn merge(
        tracked self,
        tracked other: Self,
    ) -> (tracked ret: Self)
        requires
            self.well_formed(),
            other.well_formed(),
            self@ == other@,
            self.id() == other.id(),
            self.shares() < self.total(),
            self.shares() + other.shares() <= self.total(),
        ensures
            ret@ == self@,
            ret.shares() == self.shares() + other.shares(),
            ret.well_formed(),
    {
        let new_shares = self.shares + other.shares;
        let total = self.total;
        let tracked FracPerm { mut inst, mut reader, mut frac, mut shares, total } = self;
        let oldself = self;
                let tracked (Tracked(new_reader), Tracked(new_frac)) = inst.merge(shares, other.shares, reader, other.reader, frac, other.frac);
                reader = new_reader;
                frac = new_frac;
        shares = new_shares;
        FracPerm { inst, reader, frac, shares, total }
    }

    pub proof fn extract(tracked self) -> (tracked ret: T)
        requires
            self.well_formed(),
            self.shares() == self.total(),
        ensures
            ret == self@,
    {
        let tracked FracPerm { mut inst, mut reader, mut frac, mut shares, total } = self;
        inst.take(reader, frac)
    }
}

} // verus!
