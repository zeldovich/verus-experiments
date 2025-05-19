use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    pub trait ViewEncoding : Sized {
        spec fn encoding(self) -> Seq<u8>;
    }

    pub trait Encodable
        where
            Self: Sized + View,
            <Self as View>::V: ViewEncoding,
    {
        exec fn encode(&self, buf: &mut Vec<u8>)
            ensures
                buf@ =~= old(buf)@ + self@.encoding();
    }

    pub trait Decodable
        where
            Self: Sized + View,
            <Self as View>::V: ViewEncoding,
    {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
            requires
                oldv@.encoding().is_prefix_of(old(buf)@),
            ensures
                result@ =~= oldv@,
                buf@ =~= old(buf)@.skip(oldv@.encoding().len() as int);
    }

    pub trait Serializable
        where
            Self: Sized + View + Encodable + Decodable,
            <Self as View>::V: ViewEncoding,
    {
    }

    impl ViewEncoding for u64 {
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

    impl ViewEncoding for usize {
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

    impl ViewEncoding for Seq<u8> {
        open spec fn encoding(self) -> Seq<u8> {
            (self.len() as usize).encoding() + self
        }
    }

    impl Encodable for Vec<u8> {
        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            self.len().encode(buf);
            buf.extend_from_slice(self.as_slice());
        }
    }

    impl<'a> Encodable for &'a [u8] {
        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            self.len().encode(buf);
            buf.extend_from_slice(self);
        }
    }

    impl Decodable for Vec<u8> {
        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            assert(oldv.len()@.encoding().is_prefix_of(oldv@.encoding()));
            let len = usize::decode(buf, Ghost(oldv.len()));

            assert(oldv@.is_prefix_of(oldv@.encoding().skip(oldv.len()@.encoding().len() as int)));
            let mut venc = buf.split_off(len);
            std::mem::swap(buf, &mut venc);

            venc
        }
    }
}
