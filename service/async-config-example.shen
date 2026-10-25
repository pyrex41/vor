\\ Trusted policy, chosen by the operator before any request arrives.
(load "service/config-example.shen")
(define vor.async.check
  Bytes -> (vor.check-artifact-known (vor.service.root) (vor.service.expected)
    Bytes 262144 128 65536 100000 (vor.service.symbols)))
