use vstd::prelude::*;

use super::pmem::*;
use super::pmem_impl::*;
use super::pmem_util::*;

verus! {
    fn test() {
        let (sm, Tracked(r), Tracked(d)) = SimpleMem::new(1024);
        let tracked res = Fracs{
            read: r,
            durable: d,
        };
        let Tracked(res) = sm.write::<Fracs>(0, &[0, 1, 2, 3], Tracked(res));
        assert(res.read@[0] == 0);
        let Tracked(res) = sm.write::<Fracs>(4, &[4, 5, 6, 7], Tracked(res));
        assert(res.read@[4] == 4);
        let (rvec, Tracked(res)) = sm.read::<Fracs>(2, 4, Tracked(res));
        assert(rvec@ == seq![2u8, 3, 4, 5]);
        let Tracked(res) = sm.flush::<Fracs>(Tracked(res));

        assert(res.read@[4] == 4);
        assert(res.durable@[4] == 4);
    }
}
