\\ Example verifier policy. Labels are declared identities, not image measurements.
(define claim-demo.root -> [vor-root 0 "reviewed-vor/0" "shen-scheme-43.1-pr117"])
(define claim-demo.expected
  -> [vor-claim 0 (claim-demo.root) [model (mutex.model)] []
       [[runtime unchanged-trusted-image]] boolean-states [invariant] finite-proof])
(define claim-demo.certificate
  -> [vor-certificate 0 (mutex.model) [[false false] [true false] [false true]]])
(define claim-demo.envelope
  -> [vor-evidence 0 (claim-demo.expected) (claim-demo.certificate)])
(define claim-demo.check-bytes
  [ok Bytes] -> (vor.check-artifact (claim-demo.root) (claim-demo.expected) Bytes 10000 64 10000 100)
  R -> R)
(define claim-demo.run
  -> [(claim-demo.check-bytes (vor.pack (claim-demo.envelope) 10000 64 10000))
      (vor.check-claim (claim-demo.root) (claim-demo.expected)
        [vor-evidence 0 (claim-demo.expected) [accepted finite-invariant 3]] 100)])
