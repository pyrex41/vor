\\ Controlled test corpus and results from the actual Shen checker. The audit
\\ reifies raw data, and Rocq decodes its syntax and runs the formal checker.
(load "tests/run.shen")
(define fo-audit.bytes [ok Bs] -> Bs)
(define fo-audit.write
  [] _ -> done
  [B | Bs] S -> (do (write-byte B S) (fo-audit.write Bs S)))
(define fo-audit.quote
  [] -> [nil]
  true -> [boolean true]
  false -> [boolean false]
  [H | T] -> [cell (fo-audit.quote H) (fo-audit.quote T)]
  X -> [symbol (str X)] where (symbol? X)
  X -> [text X] where (string? X)
  X -> (if (and (vor.nat? X) (<= X 65535)) [natural X] [bad-number (str X)]) where (number? X)
  _ -> [unsupported])
(define fo-audit.budgets
  _ _ _ _ [] -> []
  V G P E [Fuel | Fs] ->
    [[Fuel (= (vor.fol-check (fol-test.signature) V G P E Fuel) [accepted first-order-derivation])] |
      (fo-audit.budgets V G P E Fs)])
(define fo-audit.cases
  [] -> []
  [[case _ V G P E _] | Cs] ->
    [[case (fo-audit.quote V) (fo-audit.quote G) (fo-audit.quote P) (fo-audit.quote E)
      (fo-audit.budgets V G P E [0 1 2 3 5 8 13 21 55])] | (fo-audit.cases Cs)])
(define fo-audit.export
  -> (let S (open "build/audit/first-order.bin" out)
    (do (fo-audit.write (fo-audit.bytes (vor.pack
      [vor-first-order-audit 0 (fo-audit.quote (fol-test.signature)) (fo-audit.cases (value *fol-test-cases*))]
      1048576 256 65536)) S) (close S))))
(fo-audit.export)
