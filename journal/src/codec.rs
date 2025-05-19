use vstd::prelude::*;
use vstd::bytes::*;

verus! {
    trait Serializable : Sized + View {
        spec fn encoding(self) -> Seq<u8>;

        exec fn encode(&self, buf: &mut Vec<u8>)
            ensures
                buf@ =~= old(buf)@ + self.encoding();

        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
            requires
                oldv.encoding().is_prefix_of(old(buf)@),
            ensures
                result@ =~= oldv@,
                buf@ =~= old(buf)@.subrange(oldv.encoding().len() as int, old(buf)@.len() as int);
    }

    impl Serializable for u64 {
        spec fn encoding(self) -> Seq<u8> {
            spec_u64_to_le_bytes(self)
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

    impl Serializable for Vec<u8> {
        spec fn encoding(self) -> Seq<u8> {
            (self.len() as u64).encoding() + self@
        }

        exec fn encode(&self, buf: &mut Vec<u8>)
        {
            (self.len() as u64).encode(buf);
            buf.extend_from_slice(self.as_slice());
        }

        exec fn decode(buf: &mut Vec<u8>, Ghost(oldv): Ghost<Self>) -> (result: Self)
        {
            proof { lemma_auto_spec_u64_to_from_le_bytes(); }

            assert((oldv.len() as u64).encoding().is_prefix_of(oldv.encoding()));
            let len = u64::decode(buf, Ghost(oldv.len() as u64));
            assert(oldv.encoding().subrange(8, oldv.encoding().len() as int) == buf@.subrange(0, oldv.encoding().len() - 8));

            let mut venc = buf.split_off(len as usize);
            std::mem::swap(buf, &mut venc);

            venc
        }
    }
}
