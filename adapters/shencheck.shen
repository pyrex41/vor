\\ Trusted ShenCheck mapper. This is the sole application definition loaded
\\ by the Vör adapter. It preserves identity and payload and retains both
\\ possible outcomes when an external effect is unresolved.
(define shencheck.mapper
  [sc-observation Identity Payload [effect applied]] ->
    [possibilities [[sc-observation Identity Payload [effect applied]]]]
  [sc-observation Identity Payload [effect not-applied]] ->
    [possibilities [[sc-observation Identity Payload [effect not-applied]]]]
  [sc-observation Identity Payload [effect unknown]] ->
    [possibilities [[sc-observation Identity Payload [effect applied]]
                    [sc-observation Identity Payload [effect not-applied]]]]
  _ -> [rejected malformed-observation])
