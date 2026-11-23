(load "vor.shen")
(load "adapters/fenced-profile.shen")
(load "tests/keyed-fenced-model.shen")

(define keyed.assert
  true _ -> true
  false Why -> (simple-error (str Why)))
(define keyed.constructors
  Sort [[data Sort Cs] | _] -> Cs
  Sort [_ | Rest] -> (keyed.constructors Sort Rest))
(define keyed.nullary
  [] -> []
  [[C []] | Cs] -> [C | (keyed.nullary Cs)])
(define keyed.check-actions
  [] _ Count -> Count
  [A | As] W Count ->
    (let Expected (fj.next A W)
         Got (keyed.next A W)
      (do (keyed.assert (= Got Expected) [step-mismatch W A Expected Got])
          (keyed.check-actions As W (+ 1 Count)))))
(define keyed.check-right
  _ [] _ Count -> Count
  A [B | Bs] Actions Count ->
    (let W [fj-pair A B]
      (do (keyed.assert (= W (keyed.encode-world (keyed.decode-world W))) [world-roundtrip W])
          (keyed.check-right A Bs Actions (keyed.check-actions Actions W Count)))))
(define keyed.check-left
  [] _ _ Count -> Count
  [A | As] Slots Actions Count ->
    (keyed.check-left As Slots Actions (keyed.check-right A Slots Actions Count)))
(define keyed.shard
  [] _ _ _ -> []
  [X | Xs] Index Part Parts ->
    (if (= Index Part)
        [X | (keyed.shard Xs (keyed.advance Index Parts) Part Parts)]
        (keyed.shard Xs (keyed.advance Index Parts) Part Parts)))
(define keyed.advance
  Index Parts -> (if (= (+ Index 1) Parts) 0 (+ Index 1)))
(define keyed.check-codec
  Names Entries N ->
    (let Keys (map (/. Entry (hd Entry)) Entries)
      (keyed.assert
        (and (= N (length Names)) (and (= N (length Keys))
          (and (vor.unique? Names) (and (vor.unique? Keys) (vor.subset? Names Keys)))))
        [codec-domain Names Keys])))
(define keyed.check-action-roundtrip
  Action -> (keyed.assert
    (= Action (keyed.encode-action (keyed.find Action (value *keyed-actions*))))
    [action-roundtrip Action]))

(define keyed.allowed
  [next allow W] -> W
  R -> (simple-error (str [expected-allow R])))
(define keyed.two
  A B W -> (keyed.allowed (keyed.next B (keyed.allowed (keyed.next A W)))))
(define keyed.concurrency
  -> (let A fj-a-complete-w1-e0-pa-op0
          B fj-b-complete-w2-e1-pb-op1
          Leases [fj-pair fj-run-w1-e0-live-pa fj-run-w2-e1-live-pb]
          Done [fj-pair fj-done-e0-pa-op0-sink0 fj-done-e1-pb-op1-sink0]
          Claim fj-a-claim-w1-pa
       (do (keyed.assert (= (keyed.two A B Leases) Done) completion-a-then-b)
           (keyed.assert (= (keyed.two B A Leases) Done) completion-b-then-a)
           (keyed.assert (= (keyed.two Claim fj-expire (fj.initial))
                            [fj-pair fj-run-w1-e0-expired-pa fj-free]) claim-then-expire)
           (keyed.assert (= (keyed.two fj-expire Claim (fj.initial))
                            [fj-pair fj-run-w1-e0-live-pa fj-free]) expire-then-claim))))

(define keyed.equivalence
  Part Parts -> (let Data (fj.data)
          Slots (keyed.nullary (keyed.constructors fj-slot Data))
          Actions (keyed.nullary (keyed.constructors fj-action Data))
          Left (keyed.shard Slots 0 Part Parts)
          Expected (* (length Left) (* (length Slots) (length Actions)))
       (do (keyed.assert (and (>= Part 0) (and (< Part Parts) (<= Parts (length Slots)))) invalid-shard)
           (keyed.assert (= (keyed.constructors fj-world Data) [[fj-pair [fj-slot fj-slot]]])
                         world-constructor-domain)
           (keyed.assert (= (fj.session-start) [accepted total-admission]) admission)
           (keyed.codec-start)
           (keyed.check-codec Slots (value *keyed-slots*) 33)
           (keyed.check-codec Actions (value *keyed-actions*) 45)
           (map (function keyed.check-action-roundtrip) Actions)
           (keyed.concurrency)
           (keyed.assert (= (keyed.check-left Left Slots Actions 0) Expected) incomplete-enumeration)
           (output "keyed fenced equivalence: PASS shard ~A/~A (~A pairs)~%" Part Parts Expected))))
