\\ One-shot service entrypoint. The launcher supplies the request id and raw
\\ bytes as numeric inert data. Config functions are loaded before this entry.
(set *vor-wire* (stoutput))
(set *stoutput* (open "/dev/null" out))
(load ".tools/t-star-pr117.shen")
(if (and (= (value *version*) "43.1")
        (and (= (value *implementation*) "chez-scheme")
             (and (= (arity shen.search-user-datatypes-h) 7)
                  (= (arity shen.by-hypothesis-h) 7))))
  true (simple-error "VOR runtime guard"))
(load "vor.shen")

(define vor.service-status
  [checked _ _] -> 0
  [rejected | _] -> 1
  [violation | _] -> 1
  [unknown | _] -> 2
  _ -> 2)

(define vor.service-write
  Id Result ->
    (do (write-byte 86 (value *vor-wire*))
        (write-byte 1 (value *vor-wire*))
        (write-byte Id (value *vor-wire*))
        (write-byte (vor.service-status Result) (value *vor-wire*))))

(define vor.service-run
  Id Bytes ->
    (let Result
      (trap-error
        (vor.check-artifact-known (vor.service.root) (vor.service.expected)
          Bytes (vor.service.byte-limit) (vor.service.depth-limit)
          (vor.service.node-limit) (vor.service.proof-limit)
          (vor.service.symbols))
        (/. E [unknown service-error]))
      (vor.service-write Id Result)))

\\ argv[2] is a trusted config path selected by the launcher; argv[3] is a
\\ hexadecimal transport value, never Shen source. Decode is deliberately
\\ fixed and rejects malformed text before semantic checking.
(define vor.service-hex
  "" Acc -> (reverse Acc)
  Text Acc ->
    (let Pair (tlstr Text)
      (vor.service-hex (tlstr Pair)
        [(+ (* (vor.service-nibble (string->n (pos Text 0))) 16)
            (vor.service-nibble (string->n (pos Pair 0)))) | Acc])))

(define vor.service-nibble
  N -> (- N 48) where (<= N 57)
  N -> (- N 55) where (<= N 70)
  N -> (- N 87))

(define vor.service-hex-digit?
  N -> (or (and (>= N 48) (<= N 57))
            (or (and (>= N 65) (<= N 70)) (and (>= N 97) (<= N 102)))))
(define vor.service-hex-valid?
  "" -> true
  Text -> (let Pair (tlstr Text)
    (if (= Pair "") false
      (and (vor.service-hex-digit? (string->n (pos Text 0)))
           (and (vor.service-hex-digit? (string->n (pos Pair 0)))
                (vor.service-hex-valid? (tlstr Pair)))))))

(define vor.service-main
  [_ Config Hex] -> (if (vor.service-hex-valid? Hex)
    (do (load Config) (vor.service-request (vor.service-hex Hex [])))
    (simple-error "service hex"))
  _ -> (simple-error "service arguments"))

(define vor.service-request
  [Id | Bytes] -> (vor.service-run Id Bytes)
  _ -> (simple-error "service request"))

(vor.service-main (value *argv*))
