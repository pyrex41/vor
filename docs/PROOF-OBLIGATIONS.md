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

## Construction roadmap correspondence

The detailed program is in PLAN.md; required evidence kinds are registered in
plan/roadmap.shen. This table assigns work, not discharge status. All obligations
above remain open until exact bound derivations are checked.

| Existing obligation | Construction work |
| --- | --- |
| 1 validation | R01 identity, R03 admitted syntax, R16 validator construction |
| 2 evaluation | R03 operational adequacy, R04 data/arithmetic, R16 evaluator construction |
| 3 transitions | R07 machine construction, R08 effects, R16 semantic correspondence |
| 4 finite certificates | R07 reachable safety, R10 finite checking, R16 kernel soundness |
| 5 search | R10 rechecked results and minimization |
| 6 observations | R08 uncertainty, R10 belief adequacy, R13 adapter mapping |
| 7 propositional logic | R02 root rules, R04 induction, R16 checker soundness |
| 8 System S correspondence | R05 admission and R16 public judgment correspondence |
| 9 host preservation | R15 deployment, with explicit residual host assumptions |
| 10 adapters | R11 proof reconstruction, R13 traces, R14 implementation refinement |

New generic obligations include construction-rule soundness, total function
contracts, contract composition, invariant preservation, effect/resource
closure, assumption retention, and exact source/dependency identity. Tests of
the roadmap schema establish none of these. R17 requires the matching proof
closure and permits no conversion of test evidence into generic proof.


## R01 executable boundary additions (all open)

- Exact-claim acceptance binds every declared field and retains the assumptions
  of its checked payload; future composition must preserve dependency closure.
- `unpack(pack(v)) = v` on the admitted codec domain, and for accepted bytes,
  `pack(unpack(b)) = b`, with exactly the stated budget conditions.
- Codec validation/decoding terminates on finite bounded input; malformed,
  truncated, trailing, or exhausted input cannot yield accepted evidence.
- The public `vor-bound-evidence` judgment corresponds to the same exact-claim
  acceptance, including literal decoding and its fixed proof-depth limit.

These have executable implementations and hostile tests, not checked generic
soundness/termination proofs. The registry now adds three open R01 goals for
codec round-trip, totality, and bound correspondence (57 total goals).
