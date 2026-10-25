(load "vor.shen")
(load "service/fenced-job-config.shen")
(define fj.job-test.assert
  true _ -> true
  false Why -> (simple-error (str Why)))
(define fj.job-test-history
  -> [fj-history 0 [] [] [fj-final (fj.initial)]])
(define fj.job-test-bytes
  [ok Bytes] -> Bytes
  _ -> [])
(fj.job-test.assert (= (fj.job-request [fj-start (fj.job-test-history)])
  [unknown producer-only]) start-is-producer-only)
(let H (fj.job-test-bytes (fj.job-pack (fj.job-test-history)))
  (let R (vor.async.produce H)
    (do (fj.job-test.assert (= (hd R) produced) binary-start-produces)
        (fj.job-test.assert (> (length (hd (tl R))) 0) binary-start-has-evidence))))
(let E (fj.job-produced (fj.produce (fj.job-test-history) 512 100000))
  (do (fj.job-test.assert (= (fj.job-request [fj-observe E])
        [checked finite-history-consistency]) observe-direct)
      (let P (fj.job-pack E)
        (fj.job-test.assert (= (fj.job-request [fj-observe [fj-packed (fj.job-test-bytes P)]])
          [checked finite-history-consistency]) observe-packed))
      (let EBytes (fj.job-test-bytes (fj.job-pack E))
        (fj.job-test.assert (= (vor.async.check EBytes)
          [checked finite-history-consistency]) binary-observe))))
(fj.job-test.assert (= (fj.job-request [fj-observe [fj-evidence bad]])
  [rejected malformed-certificate]) malformed-evidence)
(print "fenced job config: PASS")
