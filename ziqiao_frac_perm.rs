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

        #[sharding(multiset)]
        pub reader: Multiset<Perm>,

        #[sharding(constant)]
        pub total: nat,     // Maximum number of shares

        #[sharding(multiset)]
        pub frac: Multiset<nat>, // assigned shares and must sum up to total.
    }

    #[invariant]
    pub fn frac_positive(&self) -> bool {
        forall |s| #[trigger]self.frac.contains(s) ==> s > 0
    }

    #[invariant]
    pub fn frac_agrees_total(&self) -> bool {
        self.storage.is_some() ==> sum(self.frac) == self.total
    }

    #[invariant]
    pub fn reader_agrees_counters(&self) -> bool {
        self.frac.len() == self.reader.len()
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |v| #[trigger] self.reader.count(v) > 0 ==> self.storage == Some(v)
    }

    init!{
        initialize_once(x: Perm, total: nat) {
            require total > 0;
            init storage = Option::Some(x);
            init reader = Multiset::empty().insert(x);
            init total = total;
            init frac = Multiset::empty().insert(total);
        }
    }

    #[inductive(initialize_once)]
    fn initialize_once_inductive(post: Self, x: Perm, total: nat) {
        let frac = Multiset::<nat>::empty().insert(total);
        lemma_sum(frac, total);
    }

    property! {
        reader_guard(x: Perm) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    transition! {
        do_share(x: Perm, shares: nat, new_shares: nat) {
            have reader >= {x};
            require(0 < new_shares < shares);
            add reader += {x};
            remove frac -= {shares};
            add frac += {new_shares};
            add frac += {(shares - new_shares) as nat};
        }
    }

    transition! {
        take(x: Perm) {
            remove reader -= {x};
            remove frac -= {pre.total};
            withdraw storage -= Some(x);
        }
    }

    #[inductive(take)]
    fn take_inductive(pre: Self, post: Self, x: Perm) {
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
    fn do_share_inductive(pre: Self, post: Self, x: Perm, shares: nat, new_shares: nat) {
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
        merge(x: Perm, shares1: nat, shares2: nat) {
            let new_shares = (shares1 + shares2) as nat;
            remove reader -= {x};
            remove reader -= {x};
            remove frac -= {shares1};
            remove frac -= {shares2};
            add reader += {x};
            add frac += {new_shares};
        }
    }


    #[inductive(merge)]
    fn merge_inductive(pre: Self, post: Self, x: Perm, shares1: nat, shares2: nat) {
        let new_shares = (shares1 + shares2) as nat;
        assert(pre.frac.contains(shares2));
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
}
spec fn wf(self) -> bool {
    predicate {
        &&& self.reader.instance_id() == self.inst.id()
        &&& self.frac.instance_id() == self.inst.id()
    }
}
}

impl<T> FracPerm<T> {
    pub closed spec fn id(self) -> InstanceId {
        self.inst.id()
    }

    pub closed spec fn view(self) -> T {
        self.reader.element()
    }

    pub closed spec fn shares(&self) -> nat {
        self.frac.element()
    }

    pub closed spec fn total(&self) -> nat {
        self.inst.total()
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
        FracPerm { inst, reader, frac }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        requires
            self.well_formed(),
        ensures
            *t == self@,
    {
        self.inst.reader_guard(self.reader.element(), &self.reader)
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
        let tracked (Tracked(r), Tracked(f1), Tracked(f2)) = self.inst.do_share(self.reader.element(), self.shares(), n, &self.reader, self.frac);
        let tracked left = FracPerm {
            inst: self.inst,
            reader: self.reader,
            frac: f1,
        };
        let tracked right = FracPerm {
            inst: self.inst,
            reader: r,
            frac: f2,
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
        let tracked (Tracked(new_reader), Tracked(new_frac)) = self.inst.merge(self.reader.element(), self.shares(), other.shares(), self.reader, other.reader, self.frac, other.frac);
        FracPerm { inst: self.inst, reader: new_reader, frac: new_frac }
    }

    pub proof fn extract(tracked self) -> (tracked ret: T)
        requires
            self.well_formed(),
            self.shares() == self.total(),
        ensures
            ret == self@,
    {
        let tracked FracPerm { mut inst, mut reader, mut frac } = self;
        inst.take(reader.element(), reader, frac)
    }
}

} // verus!
