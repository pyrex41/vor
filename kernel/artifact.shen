\\ VOR-DATA/0: bounded inert byte-list codec. Not a stdio protocol or sandbox.
\\ No read/eval/load/compiler, host callback, or artifact-supplied rule dispatch.
(tc -)

(define vor.limits?
  Bytes Depth Nodes ->
    (and (vor.nat? Bytes) (and (> Bytes 0) (and (<= Bytes 1048576)
      (and (vor.nat? Depth) (and (> Depth 0) (and (<= Depth 256)
        (and (vor.nat? Nodes) (and (> Nodes 0) (<= Nodes 65536))))))))))

(define vor.bytes?
  [] _ -> true
  [_ | _] 0 -> false
  [B | Bs] N -> (and (vor.nat? B) (and (<= B 255) (vor.bytes? Bs (- N 1))))
  _ _ -> false)

(define vor.unpack
  Bytes Limit Depth Nodes ->
    (if (vor.limits? Limit Depth Nodes)
      (if (vor.bytes? Bytes Limit)
        (trap-error (vor.dec-end (vor.dec Bytes Depth Nodes))
          (/. E [unknown codec-error]))
        [rejected invalid-or-oversized-bytes])
      [rejected invalid-codec-limits]))

(define vor.dec-end
  [decoded Value [] _] -> [ok Value]
  [decoded _ _ _] -> [rejected trailing-bytes]
  R -> R)

(define vor.dec
  _ 0 _ -> [unknown artifact-depth]
  _ _ 0 -> [unknown artifact-nodes]
  [0 | Rest] _ N -> [decoded [] Rest (- N 1)]
  [1 | Rest] _ N -> [decoded false Rest (- N 1)]
  [2 | Rest] _ N -> [decoded true Rest (- N 1)]
  [3 Hi Lo | Rest] _ N -> [decoded (+ (* Hi 256) Lo) Rest (- N 1)]
  [4 Hi Lo | Rest] _ N -> (vor.dec-text symbol (+ (* Hi 256) Lo) Rest (- N 1) "")
  [5 Hi Lo | Rest] _ N -> (vor.dec-text text (+ (* Hi 256) Lo) Rest (- N 1) "")
  [6 Hi Lo | Rest] D N ->
    (if (= (+ (* Hi 256) Lo) 0)
      [rejected noncanonical-empty-list]
      (vor.dec-list (+ (* Hi 256) Lo) Rest (- D 1) (- N 1) []))
  [] _ _ -> [rejected truncated-value]
  _ _ _ -> [rejected invalid-tag-or-header])

(define vor.dec-text
  Kind 0 Rest N Text -> (vor.dec-text-end Kind Text Rest N)
  Kind Count [B | Rest] N Text ->
    (if (if (= Kind symbol) (and (>= B 33) (<= B 126)) (<= B 127))
      (vor.dec-text Kind (- Count 1) Rest N (cn Text (n->string B)))
      [rejected invalid-text-byte])
  _ _ _ _ _ -> [rejected truncated-text])

(define vor.dec-text-end
  text Text Rest N -> [decoded Text Rest N]
  symbol "" _ _ -> [rejected empty-symbol]
  symbol Text Rest N ->
    (let S (intern Text)
      (if (and (vor.names? [S]) (= (str S) Text))
        [decoded S Rest N]
        [rejected noncanonical-symbol])))

(define vor.dec-list
  0 Rest _ N Acc -> [decoded (reverse Acc) Rest N]
  Count Rest D N Acc -> (vor.dec-list-next Count D Acc (vor.dec Rest D N)))

(define vor.dec-list-next
  Count D Acc [decoded Value Rest N] ->
    (vor.dec-list (- Count 1) Rest D N [Value | Acc])
  _ _ _ R -> R)

(define vor.pack
  Value Limit Depth Nodes ->
    (if (vor.limits? Limit Depth Nodes)
      (trap-error (vor.enc-end (vor.enc Value Depth Nodes) Limit)
        (/. E [unknown codec-error]))
      [rejected invalid-codec-limits]))

(define vor.enc-end
  [encoded Bytes _] Limit ->
    (if (vor.bytes? Bytes Limit) [ok Bytes] [rejected oversized-encoding])
  R _ -> R)

(define vor.u16 N -> (vor.u16-h N 0))
(define vor.u16-h
  N Hi -> [Hi N] where (< N 256)
  N Hi -> (vor.u16-h (- N 256) (+ Hi 1)))

(define vor.enc
  _ 0 _ -> [unknown artifact-depth]
  _ _ 0 -> [unknown artifact-nodes]
  [] _ N -> [encoded [0] (- N 1)]
  false _ N -> [encoded [1] (- N 1)]
  true _ N -> [encoded [2] (- N 1)]
  [H | T] D N ->
    (if (vor.proper? T)
      (if (<= (length [H | T]) 65535)
        (vor.enc-list-end (length [H | T])
          (vor.enc-list [H | T] (- D 1) (- N 1) []))
        [rejected list-too-long])
      [rejected improper-list])
  X _ N ->
    (if (and (vor.nat? X) (<= X 65535))
      [encoded [3 | (vor.u16 X)] (- N 1)]
      [rejected unsupported-number]) where (number? X)
  X _ N -> (vor.enc-text 5 X N) where (string? X)
  X _ N -> (vor.enc-text 4 (str X) N) where (symbol? X)
  _ _ _ -> [rejected unsupported-value])

(define vor.enc-text
  Tag Text N ->
    (if (<= (length (explode Text)) 65535)
      (vor.enc-text-end Tag (length (explode Text)) (- N 1)
        (vor.enc-chars Tag Text []))
      [rejected text-too-long]))

(define vor.enc-chars
  _ "" Acc -> [chars (reverse Acc)]
  Tag Text Acc ->
    (let B (string->n (pos Text 0))
      (if (if (= Tag 4) (and (>= B 33) (<= B 126)) (<= B 127))
        (vor.enc-chars Tag (tlstr Text) [B | Acc])
        [rejected invalid-text-byte])))

(define vor.enc-text-end
  4 0 _ _ -> [rejected empty-symbol]
  Tag Count N [chars Bytes] -> [encoded [Tag | (append (vor.u16 Count) Bytes)] N]
  _ _ _ R -> R)

(define vor.enc-list
  [] _ N Acc -> [encoded (reverse Acc) N]
  [X | Xs] D N Acc -> (vor.enc-list-next Xs D Acc (vor.enc X D N)))

(define vor.enc-list-next
  Xs D Acc [encoded Bytes N] -> (vor.enc-list Xs D N (append (reverse Bytes) Acc))
  _ _ _ R -> R)

(define vor.enc-list-end
  Count [encoded Bytes N] -> [encoded [6 | (append (vor.u16 Count) Bytes)] N]
  _ R -> R)

\\ Root and Expected are never read from the encoded envelope as authority.
(define vor.check-artifact
  Root Expected Bytes Limit Depth Nodes ProofDepth ->
    (vor.check-unpacked Root Expected (vor.unpack Bytes Limit Depth Nodes) ProofDepth))

(define vor.check-unpacked
  Root Expected [ok Artifact] D -> (vor.check-claim Root Expected Artifact D)
  _ _ R _ -> R)
