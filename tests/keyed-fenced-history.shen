\\ Run in a separate test process: only this driver redefines fj.next.
(load "tests/history-checker.shen")
(load "tests/keyed-fenced-model.shen")
(keyed.codec-start)
(set *keyed-history-calls* 0)
(define fj.next
  Action World -> (do (set *keyed-history-calls* (+ 1 (value *keyed-history-calls*)))
                      (keyed.next Action World)))
(load "tests/history-checker-controls.shen")
(hc.assert (> (value *keyed-history-calls*) 0) shadow-stepper-not-called)
(print "keyed fenced histories: PASS")
