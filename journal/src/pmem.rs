use vstd::prelude::*;
use vstd::logatom::*;
use sl::seq_view::*;
use sl::seq_helper::*;

verus! {
    pub struct PMResource {
        pub read: SeqAuth<u8>,
        pub durable: SeqAuth<u8>,
    }

    pub struct Read {
        pub read_id: int,
        pub addr: usize,
        pub num_bytes: usize,
    }

    impl ReadOperation for Read {
        type Resource = SeqAuth<u8>;
        type ExecResult = Vec<u8>;

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.read_id)
            &&& e@ == r@.subrange(self.addr as int, self.addr as int + self.num_bytes as int)
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            &&& r.valid(self.read_id)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            &&& self.addr as int + self.num_bytes as int <= r@.len()
        }
    }

    pub open spec fn can_result_from_write(post: Seq<u8>, pre: Seq<u8>, addr: int, bytes: Seq<u8>) -> bool
    {
        &&& post.len() == pre.len()
        &&& forall |i| 0 <= i < pre.len() ==> {
            ||| post[i] == pre[i]
            ||| addr <= i < addr + bytes.len() && post[i] == bytes[i-addr]
        }
    }

    pub struct Write {
        pub read_id: int,
        pub durable_id: int,
        pub addr: usize,
        pub data: Seq<u8>,
    }

    impl MutOperation for Write {
        type Resource = PMResource;
        type ExecResult = ();
        type NewState = Seq<u8>;

        open spec fn requires(self, r: Self::Resource, new_state: Self::NewState, e: Self::ExecResult) -> bool {
            &&& r.read.valid(self.read_id)
            &&& r.durable.valid(self.durable_id)
            &&& can_result_from_write(new_state, r.durable@.subrange(self.addr as int, self.addr as int + self.data.len()), 0, self.data)
        }

        open spec fn ensures(self, r: Self::Resource, new_r: Self::Resource, new_state: Self::NewState) -> bool {
            &&& new_r.read.valid(self.read_id)
            &&& new_r.durable.valid(self.durable_id)
            &&& new_r.read@ == update_seq(r.read@, self.addr as int, self.data)
            &&& new_r.durable@ == update_seq(r.durable@, self.addr as int, new_state)
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            &&& r.read.valid(self.read_id)
            &&& r.durable.valid(self.durable_id)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            &&& self.addr as int + self.data.len() <= r.read@.len()
        }
    }

    pub struct Flush {
        pub read_id: int,
        pub durable_id: int,
    }

    impl ReadOperation for Flush {
        type Resource = PMResource;
        type ExecResult = ();

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.read.valid(self.read_id)
            &&& r.durable.valid(self.durable_id)
            &&& r.read@ == r.durable@
        }
    }

    pub trait PersistentMemoryRegion : Sized
    {
        spec fn read_id(self) -> int;
        spec fn durable_id(self) -> int;

        exec fn read<Lin>(&self, addr: usize, num_bytes: usize, Tracked(lin): Tracked<Lin>) -> (result: (Vec<u8>, Tracked<Lin::Completion>))
            where
                Lin: ReadLinearizer<Read>,
            requires
                lin.pre(Read{ read_id: self.read_id(), addr, num_bytes }),
            ensures
                lin.post(Read{ read_id: self.read_id(), addr, num_bytes }, result.0, result.1@),
        ;

        exec fn write<Lin>(&self, addr: usize, bytes: &[u8], Tracked(lin): Tracked<Lin>) -> (result: Tracked<Lin::Completion>)
            where
                Lin: MutLinearizer<Write>,
            requires
                lin.pre(Write{ read_id: self.read_id(), durable_id: self.durable_id(), addr, data: bytes@ }),
            ensures
                lin.post(Write{ read_id: self.read_id(), durable_id: self.durable_id(), addr, data: bytes@ }, (), result@),
        ;

        exec fn flush<Lin>(&self, Tracked(lin): Tracked<Lin>) -> (result: Tracked<Lin::Completion>)
            where
                Lin: ReadLinearizer<Flush>,
            requires
                lin.pre(Flush{ read_id: self.read_id(), durable_id: self.durable_id() }),
            ensures
                lin.post(Flush{ read_id: self.read_id(), durable_id: self.durable_id() }, (), result@),
        ;
    }
}
