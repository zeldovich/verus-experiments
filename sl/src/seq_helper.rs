use vstd::prelude::*;

verus! {
    pub trait IntegerT : Sized {
        spec fn from_int(i: int) -> Self;
        spec fn to_int(i: Self) -> int;
    }

    impl IntegerT for int {
        open spec fn from_int(i: int) -> Self { i }
        open spec fn to_int(i: Self) -> int { i }
    }

    impl IntegerT for usize {
        open spec fn from_int(i: int) -> Self { i as usize }
        open spec fn to_int(i: Self) -> int { i as int }
    }

    pub open spec fn update_seq<V>(s: Seq<V>, off: int, v: Seq<V>) -> Seq<V> {
        Seq::new(s.len(), |i: int| if off <= i < off + v.len() { v[i - off] } else { s[i] })
    }

    pub open spec fn update_seq_map<V, I: IntegerT>(s: Seq<V>, m: Map<I, V>) -> Seq<V>
        recommends
            forall |i| m.contains_key(i) ==> 0 <= I::to_int(i) < s.len()
    {
        Seq::new(s.len(), |i: int| if m.contains_key(I::from_int(i)) { m[I::from_int(i)] } else { s[i] })
    }

    pub open spec fn seq_to_map<V, I: IntegerT>(s: Seq<V>, off: I) -> Map<I, V> {
        Map::new(|i: I| I::to_int(off) <= I::to_int(i) < I::to_int(off) + s.len(), |i: I| s[I::to_int(i)-I::to_int(off)])
    }
}
