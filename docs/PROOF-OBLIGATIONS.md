# Open proof obligations

All items below are open mechanization obligations. Passing tests does not
change that status.

1. **Validation adequacy:** every accepted model has only valid Boolean states,
   total well-scoped expressions, and well-formed simultaneous assignments.
2. **Evaluation:** the executable expression evaluator agrees with Boolean
   denotation and terminates on every validated expression.
3. **Transitions:** executable successors enumerate exactly all enabled rules
   with simultaneous updates and frame preservation.
4. **Certificate soundness:** checker acceptance implies initial inclusion,
   transition closure, and invariant truth, hence safety of all reachable states.
5. **Search:** a returned certificate passes the kernel, and a returned
   counterexample is a legal invariant-violating trace. Exhaustion never proves
   safety. Completeness is conditional on sufficient state budget/resources.
6. **Observation adequacy:** no compatible successor is lost, and every retained
   state has a predecessor and satisfies the observation. No reachability claim
   is made about an arbitrary caller-supplied belief set.
7. **Propositional soundness:** every accepted proof derives its target from its
   explicit context using the documented intuitionistic rules.
8. **System S correspondence:** supported public datatype judgments imply their
   documented model/proof facts; literal decoding cannot execute or invent a
   witness. Annotated elimination shares the explicit checker by design.
9. **Host preservation:** the Shen-Scheme compilation path preserves these
   semantics. Upstream kernel conformance is evidence only.
10. **Future adapters:** concretization/refinement maps preserve observations
    and effect ambiguity. No ShenCheck or ShenLogic integration is currently
    part of an acceptance path.

For richer domains, add partiality, errors, effects, machine arithmetic,
termination, and fairness obligations before accepting claims over them.
