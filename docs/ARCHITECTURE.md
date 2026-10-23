# Architecture

Vör defines allowed behavior as data and gives that data one executable
meaning. Search, simulation, type judgments, and external execution adapters
must refer to that same versioned model. No adapter may redefine a transition
or silently turn lack of observation into lack of effect.

The initial finite Boolean domain makes closure checking explicit without
trusting a solver, a general Shen evaluator, or a source-to-logic translator.
This is a foundation for validating the architecture, not the final domain for
cloud applications. Expanding it must preserve explicit trusted boundaries.

| Module | Responsibility |
| --- | --- |
| core | Validate model data; evaluate guards; enumerate transitions; check traces |
| certificate | Check inductive state sets; expose indexed transition evidence |
| explore | Produce certificates and concrete counterexamples |
| observe | Retain all states compatible with partial observations |
| proof | Check explicit derivations and expose indexed logical judgments |

The finite certificate checker never calls the explorer. Both consume the
same core, so tests against an independent reference are necessary: producer
and checker agreement alone cannot detect a shared semantic defect.

## Future ShenCheck boundary

ShenCheck should submit a model identity, adapter identity, ordered labelled
observations, and provenance. Initially this supports finite trace conformance.
Before timeouts, crashes, retries, or lost acknowledgements are admitted, their
alternative effects must have a declared transition interpretation. Harness
replay proves controlled-boundary reproduction, not implementation refinement.

## Future ShenLogic boundary

ShenLogic may translate Vör definitions or a supported implementation into
proof obligations. Its result must identify the exact source, translation,
assumptions, and theorem. An unverified translation or solver status cannot
be treated as a Vör kernel certificate. Translation correctness remains an
explicit obligation; the present project imports no existing proof claims.

## Why retain Shen

System S permits proof objects to inhabit behavioral judgments indexed by
specific models, contexts, and states. These judgments are executable logical
contracts. Their inference rules and trusted side conditions remain visible.
The implementation does not claim that extensible typing makes arbitrary
user-added rules sound.
