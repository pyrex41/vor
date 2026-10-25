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

(define vor.async-loop
  256 -> true
  Seq -> (let A (read-byte (stinput))
    (if (= A -1) true
      (let Size (vor.async-size A)
        (if (and (> Size 0) (<= Size 262144))
          (let Bytes (vor.async-bytes Size [])
            (let Result (trap-error (vor.async.check Bytes)
                           (/. E [unknown checker-error]))
              (do (vor.async-write Seq (vor.async-status Result))
                  (vor.async-loop (+ Seq 1)))))
          (simple-error "async payload bound"))))))

(define vor.async-main
  [_ Config] -> (do (load Config) (vor.async-write 0 0) (vor.async-loop 0))
  _ -> (simple-error "async arguments"))

(vor.async-main (value *argv*))
