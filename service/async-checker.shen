\\ Persistent trusted checker. Input is bounded inert bytes, never Shen text.
(set *vor-async-wire* (stoutput))
(set *stoutput* (open "/dev/null" out))
(load ".tools/t-star-pr117.shen")
(if (and (= (value *version*) "43.1")
        (and (= (value *implementation*) "chez-scheme")
             (and (= (arity shen.search-user-datatypes-h) 7)
                  (= (arity shen.by-hypothesis-h) 7))))
  true (simple-error "VOR runtime guard"))
(load "vor.shen")

(define vor.async-status
  [checked | _] -> 1
  [rejected | _] -> 2
  [violation | _] -> 4
  [unknown | _] -> 3
  _ -> 3)

(define vor.async-byte
  -> (let B (read-byte (stinput))
       (if (= B -1) (simple-error "truncated async input") B)))

(define vor.async-size
  A -> (+ (* A 16777216)
         (+ (* (vor.async-byte) 65536)
           (+ (* (vor.async-byte) 256) (vor.async-byte)))))

(define vor.async-bytes
  0 Acc -> (reverse Acc)
  N Acc -> (vor.async-bytes (- N 1) [(vor.async-byte) | Acc]))

(define vor.async-write
  Seq Status ->
    (do (write-byte 86 (value *vor-async-wire*))
        (write-byte 65 (value *vor-async-wire*))
        (write-byte 1 (value *vor-async-wire*))
        (write-byte Status (value *vor-async-wire*))
        (write-byte Seq (value *vor-async-wire*))))

(define vor.async-response
  [produced Bytes] -> (if (vor.bytes? Bytes 262144) [3 Bytes] [3 []])
  Result -> [(vor.async-status Result) []])
(define vor.async-request
  1 Bytes -> (vor.async.produce Bytes)
  3 Bytes -> (vor.async.check Bytes)
  _ _ -> [rejected unsupported-rpc-request])
(define vor.async-write-bytes
  [] -> true
  [B | Bs] -> (do (write-byte B (value *vor-async-wire*)) (vor.async-write-bytes Bs)))
(define vor.async-write-result
  Seq [Status Bytes] ->
    (let Size (length Bytes)
      (do (vor.async-write Seq Status)
          (write-byte 0 (value *vor-async-wire*))
          (write-byte (floor (/ Size 65536)) (value *vor-async-wire*))
          (write-byte (mod (floor (/ Size 256)) 256) (value *vor-async-wire*))
          (write-byte (mod Size 256) (value *vor-async-wire*))
          (vor.async-write-bytes Bytes))))
(define vor.async-loop
  256 -> true
  Seq -> (let A (read-byte (stinput))
    (if (= A -1) true
      (let Size (vor.async-size A)
        (if (and (> Size 0) (<= Size 262145))
          (let Kind (vor.async-byte) Bytes (vor.async-bytes (- Size 1) [])
            (let Result (trap-error (vor.async-request Kind Bytes)
                           (/. E [unknown checker-error]))
              (do (vor.async-write-result Seq (vor.async-response Result))
                  (vor.async-loop (+ Seq 1)))))
          (simple-error "async payload bound"))))))

(define vor.async-main
  [_ Config] -> (do (load Config) (vor.async-write 0 0) (vor.async-loop 0))
  _ -> (simple-error "async arguments"))

(vor.async-main (value *argv*))
