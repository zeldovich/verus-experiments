use vstd::prelude::*;

verus! {
    pub trait ReadOperation : Sized {
        type Resource /* = () */;   // tracked resource(s) passed to callback
        type ExecResult /* = () */; // executable result returned from operation

        spec fn requires(self, r: Self::Resource, e: Self::ExecResult) -> bool;

        // Optionally support peeking, which provides initial validation
        // before the operation is linearized.
        open spec fn peek_requires(self, r: Self::Resource) -> bool { true }
        open spec fn peek_ensures(self, r: Self::Resource) -> bool { true }
    }

    pub trait MutOperation : Sized {
        type Resource /* = () */;   // tracked resource(s) passed to callback
        type ExecResult /* = () */; // executable result returned from operation
        type ApplyHint /* = () */;  // when apply might otherwise be non-deterministic

        spec fn requires(self, hint: Self::ApplyHint, r: Self::Resource, e: Self::ExecResult) -> bool;
        spec fn ensures(self, hint: Self::ApplyHint, pre: Self::Resource, post: Self::Resource) -> bool;

        // Optionally support peeking, which provides initial validation
        // before the operation is linearized.
        open spec fn peek_requires(self, r: Self::Resource) -> bool { true }
        open spec fn peek_ensures(self, r: Self::Resource) -> bool { true }
    }

    pub trait ReadLinearizer<Op: ReadOperation> : Sized {
        type ApplyResult /* = () */;

        open spec fn namespaces(self) -> Set<int> {
            Set::empty()
        }

        open spec fn pre(self, op: Op) -> bool {
            true
        }

        open spec fn post(self, op: Op, r: Op::ExecResult, ar: Self::ApplyResult) -> bool {
            true
        }

        proof fn apply(tracked self, op: Op, tracked r: &Op::Resource, e: &Op::ExecResult) -> (tracked out: Self::ApplyResult)
            requires
                self.pre(op),
                op.requires(*r, *e),
            ensures
                self.post(op, *e, out),
            opens_invariants
                { self.namespaces() };

        proof fn peek(tracked &self, op: Op, tracked r: &Op::Resource)
            requires
                self.pre(op),
                op.peek_requires(*r),
            ensures
                op.peek_ensures(*r),
            opens_invariants
                { self.namespaces() };
    }

    pub trait MutLinearizer<Op: MutOperation> : Sized {
        type ApplyResult /* = () */;

        open spec fn namespaces(self) -> Set<int> {
            Set::empty()
        }

        open spec fn pre(self, op: Op) -> bool {
            true
        }

        open spec fn post(self, op: Op, r: Op::ExecResult, ar: Self::ApplyResult) -> bool {
            true
        }

        proof fn apply(tracked self, op: Op, hint: Op::ApplyHint, tracked r: &mut Op::Resource, e: &Op::ExecResult) -> (tracked out: Self::ApplyResult)
            requires
                self.pre(op),
                op.requires(hint, *old(r), *e),
            ensures
                op.ensures(hint, *old(r), *r),
                self.post(op, *e, out),
            opens_invariants
                { self.namespaces() };

        proof fn peek(tracked &self, op: Op, tracked r: &Op::Resource)
            requires
                self.pre(op),
                op.peek_requires(*r),
            ensures
                op.peek_ensures(*r),
            opens_invariants
                { self.namespaces() };
    }
}
