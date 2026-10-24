\\ Trusted test fixture export only. No artifact enters the Shen source reader.
(load "vor.shen")
(load "examples/admission.shen")
(define audit.compiled [compiled A] -> A)
(define audit.bytes [ok Bytes] -> Bytes)
(define audit.write-bytes
  [] _ -> done
  [B | Bs] Stream -> (do (write-byte B Stream) (audit.write-bytes Bs Stream)))
(define audit.export
  -> (let P (admission-demo.program)
       A (audit.compiled (vor.compile-program P))
       Stream (open "build/audit/fixtures.bin" out)
       (do (audit.write-bytes (audit.bytes (vor.pack [vor-audit-fixtures 0 P A] 1048576 256 65536)) Stream)
           (close Stream))))
(audit.export)
