(load "vor.shen")
(load "examples/effects-protocol.shen")
(set *effects-test-count* 0)
(define test.equal
  Name Actual Expected ->
    (if (= Actual Expected)
        (do (set *effects-test-count* (+ 1 (value *effects-test-count*))) passed)
        (simple-error (str Name ": expected " Expected ", got " Actual))))
(define effects.counterexample?
  [counterexample _] -> true
  _ -> false)

(test.equal (intern "healthy")
  (vor.verify (effects.model) 256)
  [accepted finite-invariant 13])
(test.equal true
  (effects.counterexample? (vor.verify (effects.brokencommit) 256)) true)
(test.equal true
  (effects.counterexample? (vor.verify (effects.brokenfinish) 256)) true)
(test.equal (intern "response-needs-durable-work")
  (vor.next (effects.model) [true false false false false false false false])
  [ok []])
(print effects-protocol-pass)
