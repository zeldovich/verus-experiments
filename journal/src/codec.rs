use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    pub trait ViewEncoding : Sized {
        spec fn encoding(self) -> Seq<u8>;
    }

    pub trait Serializable
        where
            Self: Sized + View,
    {
        open spec fn encoding(self) -> Seq<u8> { Self::view_encoding(self@) }

        spec fn view_encoding(v: Self::V) -> Seq<u8>;

        exec fn encode(&self, buf: &mut Vec<u8>)
            ensures
                buf@ =~= old(buf)@ + Self::view_encoding(self@);

        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
            requires
                Self::view_encoding(oldv@).is_prefix_of(old(buf)@),
            ensures
                result@ =~= oldv@,
                buf@ =~= old(buf)@.skip(Self::view_encoding(oldv@).len() as int);
    }

    impl Serializable for u64 {
        open spec fn view_encoding(v: u64) -> Seq<u8> {
            spec_u64_to_le_bytes(v)
        }

        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            buf.extend_from_slice(u64_to_le_bytes(*self).as_slice())
        }

        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            proof { lemma_auto_spec_u64_to_from_le_bytes(); }

            let mut venc = buf.split_off(8);
            std::mem::swap(buf, &mut venc);

            u64_from_le_bytes(venc.as_slice())
        }
    }

    impl Serializable for usize {
        open spec fn view_encoding(v: usize) -> Seq<u8> {
            u64::view_encoding(v as u64)
        }

        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            (*self as u64).encode(buf)
        }

        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            u64::decode(buf, Ghost(oldv as u64)) as usize
        }
    }

    impl Serializable for Vec<u8> {
        open spec fn view_encoding(v: Seq<u8>) -> Seq<u8> {
            usize::view_encoding(v.len() as usize) + v
        }

        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            self.len().encode(buf);
            buf.extend_from_slice(self.as_slice());
        }

        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            assert(oldv.len().encoding().is_prefix_of(oldv.encoding()));
            let len = usize::decode(buf, Ghost(oldv.len()));

            assert(oldv@.is_prefix_of(oldv.encoding().skip(oldv.len().encoding().len() as int)));
            let mut venc = buf.split_off(len);
            std::mem::swap(buf, &mut venc);

            venc
        }
    }
}
