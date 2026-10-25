\\ Trusted source capture; no artifact is evaluated by ps or the source reader.
(load "vor.shen")
(define native-audit.bytes [ok Bs] -> Bs)
(define native-audit.write
  [] _ -> done
  [B | Bs] S -> (do (write-byte B S) (native-audit.write Bs S)))
(define native-audit.export
  -> (let S (open "build/audit/native-lookup.bin" out)
    (do (native-audit.write (native-audit.bytes
      (vor.pack [vor-native-lookup 0 (ps vor.fol-at)] 1048576 256 65536)) S) (close S))))
(native-audit.export)
