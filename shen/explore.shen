\\ Untrusted search producer. Only check-certificate may accept its evidence.
(tc -)

(define vor.entry-states
  [] -> []
  [[S _] | Rest] -> [S | (vor.entry-states Rest)])

(define vor.initial-entries
  [] -> []
  [S | Ss] -> [[S [[initial S]]] | (vor.initial-entries Ss)])

(define vor.first-unsafe
  _ [] -> none
  M [[S Path] | Rest] -> (if (vor.safe? M S)
                            (vor.first-unsafe M Rest)
                            [counterexample Path]))

(define vor.fresh-entries
  [] _ _ -> []
  [[step L T] | Edges] Path Seen ->
    (if (vor.member? T Seen)
        (vor.fresh-entries Edges Path Seen)
        [[T (append Path [[step L T]])] |
          (vor.fresh-entries Edges Path [T | Seen])]))

(define vor.explore
  M Bound -> (if (vor.model? M)
                (if (and (vor.nat? Bound) (> Bound 0))
                    (if (> (length (vor.initial M)) Bound)
                        [unknown state-budget]
                        (let Entries (vor.initial-entries (vor.initial M))
                          Bad (vor.first-unsafe M Entries)
                          (if (= Bad none)
                              (vor.explore-h M Bound Entries (vor.initial M))
                              Bad)))
                    [rejected invalid-budget])
                [rejected invalid-model]))

(define vor.explore-h
  M _ [] Seen -> [certificate [vor-certificate 0 M Seen]]
  M Bound [[S Path] | Queue] Seen ->
    (let Fresh (vor.fresh-entries (vor.successors (vor.vars M) S (vor.rules M)) Path Seen)
      Bad (vor.first-unsafe M Fresh)
      (if (= Bad none)
          (let All (append Seen (vor.entry-states Fresh))
            (if (> (length All) Bound)
                [unknown state-budget]
                (vor.explore-h M Bound (append Queue Fresh) All)))
          Bad)))

(define vor.verify
  M Bound -> (vor.verify-result M (vor.explore M Bound)))

(define vor.verify-result
  M [certificate C] -> (vor.check-certificate M C)
  _ R -> R)
