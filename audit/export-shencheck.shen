\\ Trusted source capture for the actual ShenCheck mapper. The ps output is
\\ inert data; no artifact is loaded or evaluated by this exporter.
(load "vor.shen")
(load "adapters/shencheck.shen")
(define shencheck-audit.write
  [] _ -> done
  [B | Bs] S -> (do (write-byte B S) (shencheck-audit.write Bs S)))
(define shencheck-audit.export
  -> (let S (open "build/audit/shencheck-mapper.bin" out)
       (do (shencheck-audit.write
             (shencheck-audit.bytes
               (vor.pack [vor-shencheck-mapper 0 (ps shencheck.mapper)]
                 1048576 256 65536)) S)
           (close S))))
(define shencheck-audit.bytes [ok Bs] -> Bs)
(shencheck-audit.export)
