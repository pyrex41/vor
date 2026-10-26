\\ Authoritative finite VOR/0 model of request -> worker effects.
\\ Fencing is abstracted as a lease fact; worker token/generation refinement is open.
(define effects.invariant
  -> [conj [disj [neg [var accepted]] [var mutation]]
      [conj [disj [neg [var responded]] [var accepted]]
        [conj [disj [neg [var effect]] [var accepted]]
          [conj [disj [neg [var completed]] [var effect]]
            [neg [var duplicate]]]]]])
(define effects.rules
  -> [[rule request-commit [neg [var accepted]] [[accepted [lit true]] [mutation [lit true]] [obligation [lit true]]]]
      [rule respond [conj [var accepted] [var mutation]] [[responded [lit true]]]]
      [rule claim [conj [var obligation] [neg [var lease]]] [[lease [lit true]] [expired [lit false]]]]
      [rule expire [var lease] [[lease [lit false]] [expired [lit true]]]]
      [rule apply-effect [conj [var lease] [neg [var expired]]] [[effect [lit true]] [ack [lit false]]]]
      [rule acknowledge [conj [var effect] [neg [var ack]]] [[ack [lit true]]]]
      [rule lose-ack [conj [var effect] [neg [var ack]]] [[ack [lit false]]]]
      [rule crash [var lease] [[lease [lit false]] [expired [lit true]]]]
      [rule finish [conj [var lease] [conj [var effect] [var ack]]] [[completed [lit true]] [obligation [lit false]] [lease [lit false]]]]])
(define effects.model
  -> [vor-model 0 [accepted mutation obligation responded lease expired effect ack completed duplicate]
      [[false false false false false false false false false false]] (effects.rules) (effects.invariant)])
\\ Mutants retain the full action skeleton and change one action only.
(define effects.mutant-commit
  -> [vor-model 0 [accepted mutation obligation responded lease expired effect ack completed duplicate]
      [[false false false false false false false false false false]]
      [[rule request-commit [neg [var accepted]] [[accepted [lit true]] [obligation [lit true]]]]
       [rule respond [conj [var accepted] [var mutation]] [[responded [lit true]]]]
       | (tl (tl (effects.rules)))] (effects.invariant)])
(define effects.mutant-finish
  -> [vor-model 0 [accepted mutation obligation responded lease expired effect ack completed duplicate]
      [[false false false false false false false false false false]]
      [[rule request-commit [neg [var accepted]] [[accepted [lit true]] [mutation [lit true]] [obligation [lit true]]]]
       [rule respond [conj [var accepted] [var mutation]] [[responded [lit true]]]]
       [rule claim [conj [var obligation] [neg [var lease]]] [[lease [lit true]] [expired [lit false]]]]
       [rule expire [var lease] [[lease [lit false]] [expired [lit true]]]]
       [rule apply-effect [conj [var lease] [neg [var expired]]] [[effect [lit true]] [ack [lit false]]]]
       [rule acknowledge [conj [var effect] [neg [var ack]]] [[ack [lit true]]]]
       [rule lose-ack [conj [var effect] [neg [var ack]]] [[ack [lit false]]]]
       [rule crash [var lease] [[lease [lit false]] [expired [lit true]]]]
       [rule finish [var lease] [[completed [lit true]] [obligation [lit false]] [lease [lit false]]]]]
      (effects.invariant)])
(define effects.mutant-duplicate
  -> [vor-model 0 [accepted mutation obligation responded lease expired effect ack completed duplicate]
      [[false false false false false false false false false false]]
      [[rule request-commit [neg [var accepted]] [[accepted [lit true]] [mutation [lit true]] [obligation [lit true]]]]
       [rule respond [conj [var accepted] [var mutation]] [[responded [lit true]]]]
       [rule claim [conj [var obligation] [neg [var lease]]] [[lease [lit true]] [expired [lit false]]]]
       [rule expire [var lease] [[lease [lit false]] [expired [lit true]]]]
       [rule apply-effect [conj [var lease] [neg [var expired]]] [[effect [lit true]] [ack [lit false]]]]
       [rule acknowledge [conj [var effect] [neg [var ack]]] [[ack [lit true]] [duplicate [lit true]]]]
       | (tl (tl (tl (tl (tl (tl (effects.rules)))))))] (effects.invariant)])
(define effects.emit -> (print (effects.model)))
