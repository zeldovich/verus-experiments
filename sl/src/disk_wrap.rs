use vstd::prelude::*;
use super::vecdisk::*;
use super::seq_view::*;
use super::map_view::*;
use super::logatom::*;
use super::seq_helper::*;

verus! {
    pub struct DiskResources {
        pub latest: SeqAuth<u8>,
        pub persist: SeqAuth<u8>,
    }

    pub struct DiskWrap {
        d: Disk,
        r: Tracked<DiskResources>,

        // For the transactional writeset.
        writeset_auth: Tracked<MapAuth<int, u8>>,
        writeset_latest_frac: Tracked<MapFrac<int, u8>>,    // should switch to logatom
    }

    pub struct WriteOp {
        pub id: int,
        pub persist_id: int,
        pub addr: usize,
        pub data: Seq<u8>,
    }

    impl MutOperation for WriteOp {
        type Resource = DiskResources;
        type ExecResult = ();
        type ApplyHint = Seq<u8>;

        open spec fn requires(self, pstate: Seq<u8>, r: Self::Resource, e: ()) -> bool {
            &&& r.latest.valid(self.id)
            &&& r.persist.valid(self.persist_id)
            &&& can_result_from_write(pstate,
                                      if self.data.len() > 0 { r.persist@.subrange(self.addr as int, self.addr+self.data.len()) } else { Seq::empty() },
                                      0, self.data)
        }

        open spec fn ensures(self, pstate: Seq<u8>, pre: Self::Resource, post: Self::Resource) -> bool {
            &&& post.latest.valid(self.id)
            &&& post.persist.valid(self.persist_id)
            &&& post.latest@ =~= update_seq(pre.latest@, self.addr as int, self.data)
            &&& post.persist@ =~= update_seq(pre.persist@, self.addr as int, pstate)
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            &&& r.latest.valid(self.id)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            &&& self.data.len() > 0 ==> self.addr + self.data.len() <= r.latest@.len()
        }
    }

    pub struct FlushOp {
        pub id: int,
        pub persist_id: int,
    }

    impl ReadOperation for FlushOp {
        type Resource = DiskResources;
        type ExecResult = ();

        open spec fn requires(self, r: Self::Resource, e: ()) -> bool {
            &&& r.latest.valid(self.id)
            &&& r.persist.valid(self.persist_id)
            &&& r.latest@ == r.persist@
        }
    }

    pub struct ReadOp {
        pub id: int,
        pub addr: usize,
        pub len: usize,
    }

    impl ReadOperation for ReadOp {
        type Resource = SeqAuth<u8>;
        type ExecResult = Vec<u8>;

        open spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool {
            &&& r.valid(self.id)
            &&& e@ == if self.len > 0 { r@.subrange(self.addr as int, self.addr + self.len as int) } else { Seq::empty() }
        }

        open spec fn peek_requires(self, r: Self::Resource) -> bool {
            &&& r.valid(self.id)
        }

        open spec fn peek_ensures(self, r: Self::Resource) -> bool {
            &&& self.len > 0 ==> self.addr + self.len <= r@.len()
        }
    }

    impl DiskWrap {
        pub closed spec fn inv(self) -> bool
        {
            &&& self.d.inv()
            &&& self.r@.latest.inv()
            &&& self.r@.persist.inv()
            &&& self.r@.latest@ =~= self.d@
            &&& self.r@.persist@ =~= self.d.persist()
            &&& self.r@.latest@.len() == self.r@.persist@.len()

            &&& self.writeset_auth@.inv()
            &&& self.writeset_auth@@.dom() == self.writeset_latest_frac@@.dom()
            &&& self.writeset_latest_frac@.valid(self.r@.latest.id())
        }

        pub closed spec fn id(self) -> int
        {
            self.r@.latest.id()
        }

        pub closed spec fn persist_id(self) -> int
        {
            self.r@.persist.id()
        }

        pub closed spec fn writeset_id(self) -> int
        {
            self.writeset_auth@.id()
        }

        pub fn read<Lin>(&self, a: usize, len: usize,
                         Tracked(lin): Tracked<Lin>) -> (result: (Vec<u8>, Tracked<Lin::ApplyResult>))
            where
                Lin: ReadLinearizer<ReadOp>,
            requires
                self.inv(),
                lin.pre(ReadOp{ id: self.id(), addr: a, len: len }),
            ensures
                lin.post(ReadOp{ id: self.id(), addr: a, len: len }, result.0, result.1@),
        {
            proof {
                lin.peek(ReadOp{ id: self.id(), addr: a, len: len }, &self.r.borrow().latest);
            }
            let r = self.d.read(a, len);
            let lin_r = Tracked(lin.apply(ReadOp{ id: self.id(), addr: a, len: len }, &self.r.borrow().latest, &r));
            (r, lin_r)
        }

        pub fn write<Lin>(&mut self, a: usize, v: &[u8],
                          Tracked(lin): Tracked<Lin>) -> (result: Tracked<Lin::ApplyResult>)
            where
                Lin: MutLinearizer<WriteOp>,
            requires
                old(self).inv(),
                lin.pre(WriteOp{ id: old(self).id(), persist_id: old(self).persist_id(), addr: a, data: v@ }),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.persist_id() == old(self).persist_id(),
                lin.post(WriteOp{ id: old(self).id(), persist_id: old(self).persist_id(), addr: a, data: v@ }, (), result@),
        {
            proof {
                lin.peek(WriteOp{ id: old(self).id(), persist_id: old(self).persist_id(), addr: a, data: v@ }, self.r.borrow());
            }
            self.d.write(a, v);
            Tracked({
                lin.apply(WriteOp{ id: old(self).id(), persist_id: old(self).persist_id(), addr: a, data: v@ },
                          if v.len() > 0 { self.d.persist().subrange(a as int, a+v.len()) } else { Seq::empty() },
                          self.r.borrow_mut(), &())
            })
        }

        pub fn flush<Lin>(&self, Tracked(p_lin): Tracked<Lin>) -> (result: Tracked<Lin::ApplyResult>)
            where
                Lin: ReadLinearizer<FlushOp>,
            requires
                self.inv(),
                p_lin.pre(FlushOp{ id: self.id(), persist_id: self.persist_id() }),
            ensures
                p_lin.post(FlushOp{ id: self.id(), persist_id: self.persist_id() }, (), result@),
        {
            self.d.flush();
            Tracked({
                p_lin.apply(FlushOp{ id: self.id(), persist_id: self.persist_id() }, self.r.borrow(), &())
            })
        }

        pub fn new(d: Disk) -> (result: (DiskWrap, Tracked<SeqFrac<u8>>, Tracked<SeqFrac<u8>>))
            requires
                d.inv(),
                d@.len() > 0,
                d.persist().len() == d@.len(),
            ensures
                result.0.inv(),
                result.1@.valid(result.0.id()),
                result.1@.off() == 0,
                result.1@@ == d@,
                result.2@.valid(result.0.persist_id()),
                result.2@.off() == 0,
                result.2@@ == d.persist(),
        {
            let tracked (ar, fr) = SeqAuth::<u8>::new(d@);
            let tracked (par, pfr) = SeqAuth::<u8>::new(d.persist());

            let tracked (writeset_ar, writeset_fr) = MapAuth::new(Map::empty());
            let tracked writeset_latest_frac = ar.auth.empty();

            let dw = DiskWrap{
                d: d,
                r: Tracked(DiskResources{
                    latest: ar,
                    persist: par,
                }),

                writeset_auth: Tracked(writeset_ar),
                writeset_latest_frac: Tracked(writeset_latest_frac),
            };
            (dw, Tracked(fr), Tracked(pfr))
        }

        pub fn reset(&mut self) -> (writeset_id: Ghost<int>)
            requires
                old(self).inv(),
            ensures
                self.inv(),
                self.writeset_id() == writeset_id@,
        {
            let ws = self.d.reset();
            let tracked (ar, fr) = MapAuth::new(Map::empty());
            let tracked latest_frac = self.r.borrow().latest.auth.empty();

            self.writeset_auth = Tracked(ar);
            self.writeset_latest_frac = Tracked(latest_frac);

            Ghost(self.writeset_auth@.id())
        }

        pub fn write_txn(self: &mut Self, a: usize, v: &[u8], Tracked(latest): Tracked<SeqFrac<u8>>) -> (result: Tracked<SeqFrac<u8>>)
            requires
                old(self).inv(),
                latest.valid(old(self).id()),
                latest.off() == a,
                latest@.len() == v@.len(),
            ensures
                self.inv(),
                self.id() == old(self).id(),
                self.persist_id() == old(self).persist_id(),
                self.writeset_id() == old(self).writeset_id(),
                result@.valid(self.writeset_id()),
                result@.off() == a,
                result@@ =~= v@,
        {
            // XXX need to validate latest against disk's auth and the disk.inv() that says
            // all elements are in-bounds, to satisfy self.d.write_txn()'s requires.
            assume(false);

            self.d.write_txn(a, v);

            let ghost vmap = seq_to_map(v@, a as int);
            assert(vmap.dom() == Set::new(|i: int| a as int <= i < a + v@.len()));

            proof {
                self.writeset_latest_frac.borrow_mut().disjoint(&latest.frac);
            }

            let tracked mf = self.writeset_auth.borrow_mut().insert(vmap);
            assert(mf@ == vmap);

            proof {
                self.writeset_latest_frac.borrow_mut().combine(latest.frac);
            }

            Tracked(SeqFrac::new(a as nat, v@.len(), mf))
        }
    }
}
