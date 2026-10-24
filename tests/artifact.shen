\\ Exact independent wire vectors, plus generated hostile prefixes.
(define test.unpack B -> (vor.unpack B 10000 64 10000))
(define test.pack V -> (vor.pack V 10000 64 10000))
(define test.ok
  [ok X] -> X
  R -> (error "expected ok, got ~A" R))
(test.equal wire-nil (test.unpack [0]) [ok []])
(test.equal wire-false (test.unpack [1]) [ok false])
(test.equal wire-true (test.unpack [2]) [ok true])
(test.equal wire-u16 (test.unpack [3 255 255]) [ok 65535])
(test.equal wire-vector (test.unpack [6 0 3 4 0 1 112 3 0 0 2]) [ok [p 0 true]])
(test.equal encode-vector (test.pack [p 0 true]) [ok [6 0 3 4 0 1 112 3 0 0 2]])
(test.equal ascii-text (test.unpack [5 0 3 65 0 10]) [ok (cn "A" (cn (n->string 0) (n->string 10)))])
(test.equal no-list-alias (test.unpack [6 0 0]) [rejected noncanonical-empty-list])
(test.equal no-bool-alias (test.unpack [4 0 4 116 114 117 101]) [rejected noncanonical-symbol])
(test.equal no-false-alias (test.unpack [4 0 5 102 97 108 115 101]) [rejected noncanonical-symbol])
(test.equal empty-name (test.unpack [4 0 0]) [rejected empty-symbol])
(test.equal no-trailing-value (test.unpack [0 0]) [rejected trailing-bytes])
(test.equal unknown-tag (test.unpack [255]) [rejected invalid-tag-or-header])
(test.equal byte-out-of-range (test.unpack [256]) [rejected invalid-or-oversized-bytes])
(test.equal fractional-byte (test.unpack [1.5]) [rejected invalid-or-oversized-bytes])
(test.equal negative-byte (test.unpack [-1]) [rejected invalid-or-oversized-bytes])
(test.equal improper-byte-list (test.unpack [0 | bad]) [rejected invalid-or-oversized-bytes])
(test.equal invalid-symbol-char (test.unpack [4 0 1 32]) [rejected invalid-text-byte])
(test.equal invalid-text-char (test.unpack [5 0 1 128]) [rejected invalid-text-byte])
(test.equal missing-text (test.unpack [5 0 1]) [rejected truncated-text])
(test.equal incomplete-u16 (test.unpack [3 0]) [rejected invalid-tag-or-header])
(test.equal missing-value (test.unpack [6 0 1]) [rejected truncated-value])
(test.equal byte-limit (vor.unpack [6 0 1 0] 3 10 10) [rejected invalid-or-oversized-bytes])
(test.equal depth-limit (vor.unpack [6 0 1 0] 4 1 10) [unknown artifact-depth])
(test.equal node-limit (vor.unpack [6 0 1 0] 4 10 1) [unknown artifact-nodes])
(test.equal exact-limits (vor.unpack [6 0 1 0] 4 2 2) [ok [[]]])
(test.equal no-enormous-depth (vor.unpack [0] 10 257 10) [rejected invalid-codec-limits])
(test.equal zero-codec-budget (vor.unpack [0] 0 1 1) [rejected invalid-codec-limits])
(test.equal symbolic-codec-budget (vor.unpack [0] bad 1 1) [rejected invalid-codec-limits])
(test.equal encode-depth (vor.pack [[]] 4 1 2) [unknown artifact-depth])
(test.equal encode-nodes (vor.pack [[]] 4 2 1) [unknown artifact-nodes])
(test.equal encode-bytes (vor.pack [[]] 3 2 2) [rejected oversized-encoding])
(test.equal encode-improper (test.pack [x | bad]) [rejected improper-list])
(test.equal encode-closure (test.pack (/. X X)) [rejected unsupported-value])
(test.equal unsupported-real (test.pack 0.5) [rejected unsupported-number])
(test.equal unsupported-negative (test.pack -1) [rejected unsupported-number])
(test.equal unsupported-large-integer (test.pack 65536) [rejected unsupported-number])

(define test.roundtrip
  X -> (do (test.equal roundtrip (test.unpack (test.ok (test.pack X))) [ok X])
    (test.equal canonical-roundtrip
      (test.pack (test.ok (test.unpack (test.ok (test.pack X))))) (test.pack X))))
(map (function test.roundtrip) [[] true false 0 1 255 256 65535 p "" "hello" [a [b c]]])
(test.roundtrip (test.artifact))
(test.equal bound-wire
  (vor.check-artifact (test.root) (test.claim) (test.ok (test.pack (test.artifact))) 10000 64 10000 30)
  [checked (test.claim) [accepted finite-invariant 3]])
(test.equal wrong-expected-over-wire
  (vor.check-artifact (test.root) (test.logic-claim) (test.ok (test.pack (test.artifact))) 10000 64 10000 30)
  [rejected claim-mismatch])
(test.equal wire-budget-before-acceptance
  (vor.check-artifact (test.root) (test.claim) (test.ok (test.pack (test.artifact))) 10000 1 10000 30)
  [unknown artifact-depth])

\\ Every proper prefix of one COMPLETE envelope must fail to decode as a value.
(define test.prefixes
  [] _ -> done
  [B | Rest] Prefix ->
    (do (test.equal truncated-envelope (hd (test.unpack Prefix)) rejected)
      (test.prefixes Rest (append Prefix [B]))))
(test.prefixes (test.ok (test.pack
  [vor-evidence 0 (test.logic-claim) [intro [hyp]]])) [])

\\ Exhaust every single-byte tag. Only the three atomic forms are complete.
(define test.tags
  256 -> done
  N -> (do (test.equal single-byte-tag (= (hd (test.unpack [N])) ok) (< N 3))
           (test.tags (+ N 1))))
(test.tags 0)

(set *vor-injection-sentinel* untouched)
(test.equal executable-data-stays-data
  (test.unpack (test.ok (test.pack [set *vor-injection-sentinel* executed])))
  [ok [set *vor-injection-sentinel* executed]])
(test.equal no-execution-through-boundary
  (vor.check-artifact (test.root) (test.claim)
    (test.ok (test.pack [set *vor-injection-sentinel* executed])) 10000 64 10000 30)
  [rejected malformed-artifact])
(test.equal sentinel-unchanged (value *vor-injection-sentinel*) untouched)
