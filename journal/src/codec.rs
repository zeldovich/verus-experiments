use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    pub trait Encoding : Sized {
        spec fn encoding(self) -> Seq<u8>;
    }

    pub trait Encodable
        where
            Self: Sized + DeepView,
            <Self as DeepView>::V: Encoding,
    {
        exec fn encode(&self, buf: &mut Vec<u8>)
            ensures
                buf@ =~= old(buf)@ + self.deep_view().encoding();
    }

    pub trait Decodable
        where
            Self: Sized + DeepView,
            <Self as DeepView>::V: Encoding,
    {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
            requires
                oldv.deep_view().encoding().is_prefix_of(old(buf)@),
            ensures
                result.deep_view() =~= oldv.deep_view(),
                buf@ =~= old(buf)@.skip(oldv.deep_view().encoding().len() as int);
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

    impl<'a> Encodable for &'a [u8] {
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

    impl Decodable for Vec<u8> {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            broadcast use is_prefix_of_trans;
            broadcast use seq_u8_encoding_simplify;

            let len = usize::decode(buf, Ghost(oldv.len()));

            assert(oldv.deep_view().is_prefix_of(oldv.deep_view().encoding().skip(oldv.len().deep_view().encoding().len() as int)));
            let mut venc = buf.split_off(len);
            std::mem::swap(buf, &mut venc);

            venc
        }
    }
}
