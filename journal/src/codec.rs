use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    pub trait Encoding : Sized {
        open spec fn encodable(self) -> bool { true }
        spec fn encoding(self) -> Seq<u8>;
    }

    pub trait Encodable
        where
            Self: Sized + DeepView,
            <Self as DeepView>::V: Encoding,
    {
        exec fn encode(&self, buf: &mut Vec<u8>)
            ensures
                buf@ =~= old(buf)@ + self.deep_view().encoding(),
                self.deep_view().encodable();
    }

    pub trait Decodable
        where
            Self: Sized + DeepView,
            <Self as DeepView>::V: Encoding,
    {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldview): Ghost<<Self as DeepView>::V>) -> (result: Self)
            requires
                oldview.encodable(),
                oldview.encoding().is_prefix_of(old(buf)@),
            ensures
                result.deep_view() =~= oldview,
                buf@ =~= old(buf)@.skip(oldview.encoding().len() as int);
    }

    pub trait Serializable
        where
            Self: Sized + DeepView + Encodable + Decodable,
            <Self as DeepView>::V: Encoding,
    {
    }

    impl Encoding for u8 {
        open spec fn encoding(self) -> Seq<u8> {
            seq![self]
        }
    }

    impl Encoding for u64 {
        open spec fn encoding(self) -> Seq<u8> {
            spec_u64_to_le_bytes(self)
        }
    }

    impl Encodable for u64 {
        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            buf.extend_from_slice(u64_to_le_bytes(*self).as_slice())
        }
    }

    impl Decodable for u64 {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            proof { lemma_auto_spec_u64_to_from_le_bytes(); }

            let mut venc = buf.split_off(8);
            std::mem::swap(buf, &mut venc);

            u64_from_le_bytes(venc.as_slice())
        }
    }

    impl Encoding for usize {
        open spec fn encoding(self) -> Seq<u8> {
            (self as u64).encoding()
        }
    }

    impl Encodable for usize {
        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            (*self as u64).encode(buf)
        }
    }

    impl Decodable for usize {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            u64::decode(buf, Ghost(oldv as u64)) as usize
        }
    }

    impl<T> Encoding for Seq<T>
        where
            T: Encoding,
    {
        open spec fn encodable(self) -> bool {
            self.len() as usize == self.len()
        }

        open spec fn encoding(self) -> Seq<u8> {
            (self.len() as usize).encoding() + self.map(|i: int, v: T| v.encoding()).flatten()
        }
    }

    pub open spec fn seq_u8_encoding_simpler(s: Seq<u8>) -> Seq<u8> {
        (s.len() as usize).encoding() + s
    }

    pub proof fn flatten_encoding_u8(v: Seq<u8>)
        ensures
            v =~= v.map(|i: int, v: u8| v.encoding()).flatten()
        decreases
            v.len()
    {
        if v.len() == 0 {
        } else {
            assert(v.map(|i: int, v: u8| v.encoding()).drop_first() == v.drop_first().map(|i: int, v: u8| v.encoding()));
            flatten_encoding_u8(v.drop_first());
        }
    }

    pub broadcast proof fn seq_u8_encoding_simplify(s: Seq<u8>)
        ensures
            #[trigger] s.encoding() == seq_u8_encoding_simpler(s)
    {
        flatten_encoding_u8(s);
    }

    impl Encodable for Vec<u8> {
        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            broadcast use seq_u8_encoding_simplify;

            self.len().encode(buf);
            buf.extend_from_slice(self.as_slice());
        }
    }

    pub trait VecLoopEncode {}

    impl<T> Encodable for Vec<T>
        where
            T: Encodable + DeepView + VecLoopEncode,
            <T as DeepView>::V: Encoding,
    {
        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            self.len().encode(buf);
            for i in 0..self.len()
                invariant
                    buf@ =~= old(buf)@ + (self.deep_view().len() as usize).encoding() + self.deep_view().take(i as int).map(|i: int, v: <T as DeepView>::V| v.encoding()).flatten()
            {
                self[i].encode(buf);
                proof {
                    self.deep_view().take(i as int).map(|i: int, v: <T as DeepView>::V| v.encoding()).lemma_flatten_and_flatten_alt_are_equivalent();
                    self.deep_view().take(i+1).map(|i: int, v: <T as DeepView>::V| v.encoding()).lemma_flatten_and_flatten_alt_are_equivalent();
                }
                assert(self.deep_view().take(i+1).map(|i: int, v: <T as DeepView>::V| v.encoding()) == self.deep_view().map(|i: int, v: <T as DeepView>::V| v.encoding()).take(i+1));
                assert(self.deep_view().take(i+1).drop_last().map(|i: int, v: <T as DeepView>::V| v.encoding()) == self.deep_view().map(|i: int, v: <T as DeepView>::V| v.encoding()).take(i+1).drop_last());
                assert(self.deep_view().take(i+1).drop_last() == self.deep_view().take(i as int));
            }
            assert(self.deep_view() == self.deep_view().take(self.len() as int));
        }
    }

    impl Encodable for &[u8] {
        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            broadcast use seq_u8_encoding_simplify;

            self.len().encode(buf);
            buf.extend_from_slice(self);
        }
    }

    pub broadcast proof fn is_prefix_of_trans<T>(a: Seq<T>, c: Seq<T>)
        requires
            ({
                ||| exists |b: Seq<T>| a.is_prefix_of(b) && #[trigger] b.is_prefix_of(c)
                ||| exists |b: Seq<T>| #[trigger] a.is_prefix_of(b) && b.is_prefix_of(c)
            })
        ensures
            #[trigger] a.is_prefix_of(c),
    {}

    pub broadcast proof fn is_prefix_of_skip<T>(a: Seq<T>, b: Seq<T>, c: Seq<T>, n: int)
        requires
            0 <= n <= b.len(),
        ensures
            a.is_prefix_of(b.skip(n)) && #[trigger] b.is_prefix_of(c) ==> #[trigger] a.is_prefix_of(c.skip(n)),
    {}

    pub trait VecLoopDecode {}

    impl<T> Decodable for Vec<T>
        where
            T: Decodable + DeepView + VecLoopDecode,
            <T as DeepView>::V: Encoding,
    {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldview): Ghost<<Self as DeepView>::V>) -> (result: Self)
        {
            broadcast use is_prefix_of_trans;
            broadcast use is_prefix_of_skip;

            let len = usize::decode(buf, Ghost(oldview.len() as usize));
            let mut result = Vec::<T>::new();

            assert(result.deep_view() == oldview.take(0));
            assert(oldview.skip(0) == oldview);

            for i in 0..len
                invariant
                    len == oldview.len(),
                    result.deep_view() == oldview.take(i as int),
                    buf@ =~= old(buf)@.skip((oldview.len() as usize).encoding().len() as int +
                                            oldview.take(i as int).map(|i: int, v: <T as DeepView>::V| v.encoding()).flatten().len()),
                    oldview.skip(i as int).map(|i: int, v: <T as DeepView>::V| v.encoding()).flatten().is_prefix_of(buf@),
            {
                // XXX
                proof { admit(); }

                let e = T::decode(buf, Ghost(oldview[i as int]));
                result.push(e);
                assert(e.deep_view() == oldview[i as int]);
                assert(result.deep_view() == oldview.take(i as int).push(e.deep_view()));
                assert(result.deep_view() == oldview.take(i+1));
            }

            result
        }
    }

    impl Decodable for Vec<u8> {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldview): Ghost<<Self as DeepView>::V>) -> (result: Self)
        {
            broadcast use is_prefix_of_trans;
            broadcast use seq_u8_encoding_simplify;

            let len = usize::decode(buf, Ghost(oldview.len() as usize));

            assert(oldview.is_prefix_of(oldview.encoding().skip((oldview.len() as usize).encoding().len() as int)));
            let mut venc = buf.split_off(len);
            std::mem::swap(buf, &mut venc);

            venc
        }
    }
}
