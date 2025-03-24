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

impl<T> SumTrait for (T, nat) {
    open spec fn count(&self) -> nat {
        self.1
    }
}

} // verus!

tokenized_state_machine!(ref_counter<Perm> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<Perm>,

        #[sharding(multiset)]
        pub reader: Multiset<(Perm, nat)>,  // read token and number of shares

        #[sharding(constant)]
        pub total: nat,                     // maximum number of shares, must be sum of readers
    }

    #[invariant]
    pub fn frac_positive(&self) -> bool {
        forall |s| #[trigger] self.reader.count(s) > 0 ==> s.1 > 0
    }

    #[invariant]
    pub fn frac_agrees_total(&self) -> bool {
        self.storage.is_some() ==> sum(self.reader) == self.total
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |v| #[trigger] self.reader.count(v) > 0 ==> self.storage == Some(v.0)
    }

    init!{
        initialize_once(x: Perm, total: nat) {
            require total > 0;
            init storage = Option::Some(x);
            init reader = Multiset::empty().insert((x, total));
            init total = total;
        }
    }

    #[inductive(initialize_once)]
    fn initialize_once_inductive(post: Self, x: Perm, total: nat) {
        let frac = Multiset::empty().insert((x, total));
        lemma_sum(frac, (x, total));
    }

    property! {
        reader_guard(x: Perm, shares: nat) {
            have reader >= {(x, shares)};
            guard storage >= Some(x);
        }
    }

    transition! {
        do_share(x: Perm, shares: nat, new_shares: nat) {
            remove reader -= {(x, shares)};
            require(0 < new_shares < shares);
            add reader += {(x, new_shares)};
            add reader += {(x, (shares - new_shares) as nat)};
        }
    }

    transition! {
        take(x: Perm) {
            remove reader -= {(x, pre.total)};
            withdraw storage -= Some(x);
        }
    }

    #[inductive(take)]
    fn take_inductive(pre: Self, post: Self, x: Perm) {
        lemma_sum(pre.reader, (x, pre.total));
        let reader1 = pre.reader.remove((x, pre.total));
        assert(reader1.len() == 0) by {
            let e = reader1.choose();
            if (reader1.contains(e)) {
                lemma_sum(reader1, e);
            }
        }
    }

    #[inductive(do_share)]
    fn do_share_inductive(pre: Self, post: Self, x: Perm, shares: nat, new_shares: nat) {
        let reader1 = pre.reader.remove((x, shares));
        let reader2 = reader1.insert((x, new_shares));
        lemma_sum(pre.reader, (x, shares));
        lemma_sum_insert(reader1, (x, new_shares));
        lemma_sum_insert(reader2, (x, (shares - new_shares) as nat));
    }

    transition!{
        merge(x: Perm, shares1: nat, shares2: nat) {
            let new_shares = (shares1 + shares2) as nat;
            remove reader -= {(x, shares1)};
            remove reader -= {(x, shares2)};
            add reader += {(x, new_shares)};
        }
    }

    #[inductive(merge)]
    fn merge_inductive(pre: Self, post: Self, x: Perm, shares1: nat, shares2: nat) {
        let new_shares = (shares1 + shares2) as nat;
        let reader1 = pre.reader.remove((x, shares1));
        let reader2 = reader1.remove((x, shares2));
        lemma_sum(pre.reader, (x, shares1));
        lemma_sum(reader1, (x, shares2));
        lemma_sum_insert(reader2, (x, (shares1 + shares2) as nat));
    }
});

#[cfg(verus_keep_ghost)]
verus! {

struct_with_invariants!{
/// A `tracked ghost` container that you can put a ghost object in.
/// A `Shared<T>` is duplicable and lets you get a `&T` out.
pub tracked struct FracPerm<T> {
    tracked inst: ref_counter::Instance<T>,
    tracked reader: ref_counter::reader<T>,
}
spec fn wf(self) -> bool {
    predicate {
        self.reader.instance_id() == self.inst.id()
    }
}
}

impl<T> FracPerm<T> {
    pub closed spec fn id(self) -> InstanceId {
        self.inst.id()
    }

    pub closed spec fn view(self) -> T {
        self.reader.element().0
    }

    pub closed spec fn shares(&self) -> nat {
        self.reader.element().1
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
        let tracked (Tracked(inst), Tracked(mut readers)) =
            ref_counter::Instance::initialize_once(t, total, Some(t));
        let tracked reader = readers.remove((t, total));
        FracPerm { inst, reader }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        requires
            self.well_formed(),
        ensures
            *t == self@,
    {
        self.inst.reader_guard(self.view(), self.shares(), &self.reader)
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
        let tracked (Tracked(r1), Tracked(r2)) = self.inst.do_share(self.view(), self.shares(), n, self.reader);
        let tracked left = FracPerm {
            inst: self.inst,
            reader: r1,
        };
        let tracked right = FracPerm {
            inst: self.inst,
            reader: r2,
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
        let tracked (new_reader) = self.inst.merge(self.view(), self.shares(), other.shares(), self.reader, other.reader);
        FracPerm { inst: self.inst, reader: new_reader }
    }

    pub proof fn extract(tracked self) -> (tracked ret: T)
        requires
            self.well_formed(),
            self.shares() == self.total(),
        ensures
            ret == self@,
    {
        let tracked FracPerm { mut inst, mut reader } = self;
        inst.take(reader.element().0, reader)
    }
}

} // verus!
