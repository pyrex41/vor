\\ The acceptance kernel: check a finite inductive set against an EXACT model.
\\ Does not call the explorer or trust its status, counts, or reachability.
(tc -)

(define vor.subset?
  [] _ -> true
  [S | Ss] States -> (and (vor.member? S States) (vor.subset? Ss States)))

(define vor.targets-in?
  [] _ -> true
  [[step _ S] | Edges] States ->
    (and (vor.member? S States) (vor.targets-in? Edges States)))

(define vor.closed-safe?
  _ [] _ -> true
  M [S | Ss] States ->
    (and (vor.safe? M S)
         (and (vor.targets-in? (vor.successors (vor.vars M) S (vor.rules M)) States)
              (vor.closed-safe? M Ss States))))

(define vor.check-certificate
  M C -> (if (vor.model? M)
             (vor.check-certificate-h M C)
             [rejected invalid-model]))

(define vor.check-certificate-h
  M [vor-certificate 0 M States] ->
    (if (and (vor.states? (vor.vars M) States) (vor.unique? States))
        (if (vor.subset? (vor.initial M) States)
            (if (vor.closed-safe? M States States)
                [accepted finite-invariant (length States)]
                [rejected not-closed-or-unsafe])
            [rejected missing-initial-state])
        [rejected invalid-state-set])
  _ _ -> [rejected certificate-model-or-version-mismatch])

\\ Executable behavioral judgments: proof types indexed by model AND endpoints.
\\ These rules call the kernel, never the searcher. The conditional rule's
\\ soundness relies on the same explicitly documented semantic implementation.
(datatype vor-evidence
  if (vor.model? M)
  if (vor.state? (vor.vars M) S)
  if (vor.member? S (vor.initial M))
  if (= (vor.decode-literal E) [ok [initial S]])
  _______________________________________________
  E : (vor-initial M S);

  if (vor.model? M)
  if (vor.state? (vor.vars M) S)
  if (vor.member? [step L T] (vor.successors (vor.vars M) S (vor.rules M)))
  if (= (vor.decode-literal E) [ok [step L T]])
  _________________________________________________________________
  E : (vor-step M S L T);

  if (vor.model? M)
  if (vor.state? (vor.vars M) S)
  if (vor.safe? M S)
  if (= (vor.decode-literal E) [ok [safe S]])
  _______________________________________________
  E : (vor-safe M S);)
