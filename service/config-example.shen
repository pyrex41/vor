\\ Trusted startup policy example. Deployments should provide their own
\\ reviewed config and pass its path before any request is read.
(load "examples/mutex.shen")
(define vor.service.root -> [vor-root 0 "reviewed-vor/0" "shen-scheme-43.1-pr117"])
(define vor.service.expected
  -> [vor-claim 0 (vor.service.root) [model (mutex.model)] []
       [[runtime unchanged-trusted-image]] boolean-states [invariant] finite-proof])
(define vor.service.symbols
  -> [vor-root vor-claim vor-certificate vor-evidence vor-model model mutex
      alice bob neg var lit rule conj initial alice-enter alice-leave bob-enter bob-leave
      invariant finite-proof runtime unchanged-trusted-image boolean-states])
(define vor.service.byte-limit -> 8192)
(define vor.service.depth-limit -> 64)
(define vor.service.node-limit -> 10000)
(define vor.service.proof-limit -> 100)
