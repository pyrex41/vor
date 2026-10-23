\\ Proof-carrying intuitionistic propositional logic. No admit/axiom rule.
\\ Context membership is explicit; assumptions cannot leak from imp-intro.
(tc -)

(define vor.formula?
  [truth] -> true
  [falsehood] -> true
  [atom P] -> (vor.names? [P])
  [both P Q] -> (and (vor.formula? P) (vor.formula? Q))
  [implies P Q] -> (and (vor.formula? P) (vor.formula? Q))
  _ -> false)

(define vor.context?
  empty -> true
  [assuming P G] -> (and (vor.formula? P) (vor.context? G))
  _ -> false)

(define vor.hyp?
  _ empty -> false
  P [assuming Q G] -> (or (= P Q) (vor.hyp? P G))
  _ _ -> false)

(define vor.proof
  Gamma P Evidence Depth ->
    (if (and (vor.context? Gamma) (vor.formula? P))
        (if (vor.nat? Depth)
            (vor.proof-h Gamma P Evidence Depth)
            [rejected invalid-budget])
        [rejected malformed-sequent]))

(define vor.proof-h
  _ _ _ 0 -> [unknown proof-depth]
  G P [hyp] _ -> (if (vor.hyp? P G) [accepted derivation] [rejected hypothesis])
  _ [truth] [unit] _ -> [accepted derivation]
  G [both P Q] [pair A B] D ->
    (vor.proof-and (vor.proof-h G P A (- D 1)) (vor.proof-h G Q B (- D 1)))
  G [implies P Q] [intro A] D -> (vor.proof-h [assuming P G] Q A (- D 1))
  G Q [apply P A B] D ->
    (if (vor.formula? P)
        (vor.proof-and (vor.proof-h G [implies P Q] A (- D 1))
                       (vor.proof-h G P B (- D 1)))
        [rejected malformed-formula])
  G P [left Q A] D ->
    (if (vor.formula? Q)
        (vor.proof-h G [both P Q] A (- D 1))
        [rejected malformed-formula])
  G Q [right P A] D ->
    (if (vor.formula? P)
        (vor.proof-h G [both P Q] A (- D 1))
        [rejected malformed-formula])
  G _ [absurd A] D -> (vor.proof-h G [falsehood] A (- D 1))
  _ _ _ _ -> [rejected invalid-proof])

(define vor.proof-and
  [accepted derivation] [accepted derivation] -> [accepted derivation]
  [rejected Why] _ -> [rejected Why]
  _ [rejected Why] -> [rejected Why]
  _ _ -> [unknown proof-depth])

\\ System S sees proof annotations as cons syntax, not evaluated data.
\\ Decode that syntax explicitly for annotated elimination rules only.
(define vor.decode-literal
  [cons H T] -> (vor.decode-cons (vor.decode-literal H) (vor.decode-literal T))
  X -> [ok X] where (or (symbol? X) (or (= X []) (or (= X true) (= X false))))
  _ -> [rejected nonliteral])

(define vor.decode-cons
  [ok H] [ok T] -> [ok [H | T]]
  _ _ -> [rejected nonliteral])

(define vor.elimination-code?
  E -> (vor.elimination? (vor.decode-literal E)))

(define vor.elimination?
  [ok [apply _ _ _]] -> true
  [ok [left _ _]] -> true
  [ok [right _ _]] -> true
  _ -> false)

(define vor.check-elimination
  E G P -> (vor.check-decoded (vor.decode-literal E) G P))

(define vor.check-decoded
  [ok Evidence] G P -> (= (vor.proof G P Evidence 1000) [accepted derivation])
  _ _ _ -> false)

\\ Context- and proposition-indexed types. Introductions are inference rules;
\\ annotated eliminations delegate to the explicit kernel after literal decoding.
(datatype vor-logic
  if (vor.context? G)
  if (vor.formula? P)
  A : (vor-derives G P);
  ___________________________________________
  A : (vor-proves G P);

  if (vor.formula? P)
  if (vor.hyp? P G)
  _________________________________
  [hyp] : (vor-derives G P);

  _________________________________
  [unit] : (vor-derives G (truth));

  A : (vor-derives G P); B : (vor-derives G Q);
  ___________________________________________
  [pair A B] : (vor-derives G (both P Q));

  A : (vor-derives (assuming P G) Q);
  ___________________________________________
  [intro A] : (vor-derives G (implies P Q));

  if (vor.elimination-code? E)
  if (vor.check-elimination E G P)
  ___________________________________________
  E : (vor-derives G P);

  A : (vor-derives G (falsehood));
  ___________________________________________
  [absurd A] : (vor-derives G P);)

\\ The public type-checking entry point accepts data, not executable source.
\\ Only VOR judgments are admitted. Host inference failure is uncertainty.
(define vor.judgment?
  [vor-proves G P] -> (and (vor.context? G) (vor.formula? P))
  [vor-initial M S] -> (and (vor.model? M) (vor.state? (vor.vars M) S))
  [vor-safe M S] -> (and (vor.model? M) (vor.state? (vor.vars M) S))
  [vor-step M S L T] ->
    (and (vor.model? M)
      (and (vor.state? (vor.vars M) S)
        (and (vor.names? [L]) (vor.state? (vor.vars M) T))))
  _ -> false)

(define vor.typecheck
  Evidence Judgment ->
    (if (vor.judgment? Judgment)
        (trap-error
          (if (vor.system-s? Evidence Judgment)
              [accepted typed-evidence]
              [rejected invalid-evidence])
          (/. E [unknown typechecker-error]))
        [rejected malformed-judgment]))

(define vor.system-s?
  Evidence Judgment ->
    (let Term (shen.curry (shen.rcons_form Evidence))
      Sequent [Term : Judgment]
      (prolog? (shen.system-S (receive Sequent) []))))
