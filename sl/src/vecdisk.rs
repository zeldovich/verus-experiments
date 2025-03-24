use vstd::prelude::*;
use super::seq_helper::*;
use std::collections::HashMap;

verus! {
    broadcast use vstd::std_specs::hash::group_hash_axioms;

    pub struct Disk {
        store: Vec<u8>,
        persist: Ghost<Seq<u8>>,
        writeset: HashMap<usize, u8>,
    }

    pub open spec fn can_result_from_write(post: Seq<u8>, pre: Seq<u8>, addr: int, bytes: Seq<u8>) -> bool
    {
        &&& post.len() == pre.len()
        &&& forall |i| 0 <= i < pre.len() ==> {
            ||| post[i] == pre[i]
            ||| addr <= i < addr + bytes.len() && post[i] == bytes[i-addr]
        }
    }

    #[verifier::external_body]
    pub fn copy_from_slice(bytes: &[u8]) -> (out: Vec<u8>)
        ensures
            out@ == bytes@
    {
        let mut buffer = vec![0; bytes.len()];
        let mut buffer_slice = buffer.as_mut_slice();
        buffer_slice.copy_from_slice(bytes);
        buffer
    }

    impl Disk {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.persist@.len() == self.store@.len()
            &&& forall |i: usize| self.writeset@.contains_key(i) ==> i < self.store@.len()
        }

        pub closed spec fn view(self) -> Seq<u8>
        {
            self.store@
        }

        pub closed spec fn writeset(self) -> Map<usize, u8>
        {
            self.writeset@
        }

        pub closed spec fn persist(self) -> Seq<u8>
        {
            self.persist@
        }

        pub proof fn disklen(self) -> (result: usize)
            ensures
                result == self@.len(),
        {
            vstd::std_specs::vec::axiom_spec_len(&self.store);
            self@.len() as usize
        }

        pub fn read_one(&self, a: usize) -> (result: u8)
            requires
                self.inv(),
                a < self@.len(),
            ensures
                result == self@[a as int]
        {
            self.store[a]
        }

        pub fn write_one(&mut self, a: usize, v: u8)
            requires
                old(self).inv(),
                a < old(self)@.len()
            ensures
                self.inv(),
                self@ == old(self)@.update(a as int, v),
                can_result_from_write(self.persist(), old(self).persist(), a as int, seq![v]),
        {
            // XXX Where is Vec::set() coming from?
            self.store.set(a, v);

            proof {
                let persist_prophecy: bool = arbitrary();
                if persist_prophecy {
                    *self.persist.borrow_mut() = self.persist@.update(a as int, v);
                }
            }
        }

        #[verifier::external_body]
        pub fn read(&self, a: usize, len: usize) -> (result: Vec<u8>)
            requires
                self.inv(),
                len > 0 ==> a + len <= self@.len(),
            ensures
                result@ == if len > 0 { self@.subrange(a as int, a + len as nat) } else { Seq::empty() },
        {
            copy_from_slice(&self.store[a..a+len])
        }

        #[verifier::external_body]
        pub fn write(&mut self, a: usize, v: &[u8])
            requires
                old(self).inv(),
                v@.len() > 0 ==> a + v@.len() <= old(self)@.len(),
            ensures
                self.inv(),
                self@ == update_seq(old(self)@, a as int, v@),
                can_result_from_write(self.persist(), old(self).persist(), a as int, v@),
        {
            self.store.splice(a..a+v.len(), v.iter().cloned());
            self.persist = arbitrary();
        }

        #[verifier::external_body]
        pub fn flush(&self)
            requires
                self.inv(),
            ensures
                self.persist() == self@,
        {
            proof {
                // *self.persist.borrow_mut() = self.store@;
            }
        }

        pub fn new(n: usize) -> (result: Disk)
            ensures
                result.inv(),
                result@ =~= Seq::<u8>::new(n as nat, |i: int| 0),
                result.persist() == result@,
        {
            let mut store = Vec::new();
            store.resize(n, 0);
            Disk{
                store: store,
                persist: Ghost(store@),
                writeset: HashMap::new(),
            }
        }

        pub fn reset(self: &mut Self)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self@ == old(self)@,
                self.persist() == old(self).persist(),
                self.writeset() == Map::<usize, u8>::empty(),
        {
            self.writeset = HashMap::new();
        }

        pub fn write_txn(self: &mut Self, a: usize, v: &[u8])
            requires
                old(self).inv(),
                v@.len() > 0 ==> a + v@.len() <= old(self)@.len(),
            ensures
                self.inv(),
                self@ == old(self)@,
                self.writeset() =~= old(self).writeset().union_prefer_right(seq_to_map(v@, a)),
        {
            broadcast use vstd::map::group_map_axioms;

            for i in 0..v.len()
                invariant
                    self.inv(),
                    self@ == old(self)@,
                    v@.len() > 0 ==> a + v@.len() <= old(self)@.len(),
                    self.writeset() =~= old(self).writeset().union_prefer_right(seq_to_map(v@.subrange(0, i as int), a)),
            {
                proof {
                    // Prove that self@.len() is at most usize, which means no overflows.
                    vstd::std_specs::vec::axiom_spec_len(&self.store);
                }

                self.writeset.insert(a+i, v[i]);
            }
        }

        #[verifier::external_body]
        pub fn commit(&mut self)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self@ == update_seq_map(old(self)@, old(self).writeset()),
                self.persist() == update_seq_map(old(self).persist(), old(self).writeset()),
                self.writeset() == Map::<usize, u8>::empty(),
        {
            for (&a, &v) in self.writeset.iter() {
                self.store.set(a, v);

                proof {
                    *self.persist.borrow_mut() = self.persist@.update(a as int, v);
                }
            }

            self.writeset = HashMap::new();

            // XXX prove later
        }
    }
}
