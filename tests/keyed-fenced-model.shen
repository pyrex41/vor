\\ Test-only shadow of the admitted fenced-job profile. A world is an
\\ association list from [tenant job] to a unique job record.
(tc -)

\\ Local rules see only the record that they replace.
(define keyed.local
  [claim W P] [free] -> [allow [running W e0 live P]]
  [claim W P] [running _ e0 expired _] -> [allow [running W e1 live P]]
  [claim _ _] [running _ e1 expired _] -> [unknown profile-epoch-bound]
  [complete W E P O] [running W E live P] -> [allow [done E P O sink0]]
  [complete _ _ P O] [done E P O S] -> [allow [done E P O S]]
  [deliver P] [done E P O _] -> [allow [done E P O sink1]]
  _ Record -> [deny Record])

\\ The one global rule in this profile: both leases expire in a single step.
(define keyed.expire-record
  [running W E live P] -> [running W E expired P]
  Record -> Record)
(define keyed.expire
  [] -> []
  [[K R] | Rest] -> [[K (keyed.expire-record R)] | (keyed.expire Rest)])

(define keyed.frame
  K R [[K _] | Rest] -> [[K R] | Rest]
  K R [Entry | Rest] -> [Entry | (keyed.frame K R Rest)])
(define keyed.find
  K [[K R] | _] -> R
  K [_ | Rest] -> (keyed.find K Rest))
(define keyed.step
  [expire] World -> [next allow (keyed.expire World)]
  [at K Rule] World ->
    (keyed.replace (keyed.local Rule (keyed.find K World)) K World))
(define keyed.replace
  [unknown Reason] _ _ -> [unknown Reason]
  [Verdict Record] K World -> [next Verdict (keyed.frame K Record World)])

\\ Finite compatibility codec. Constructor spelling is kept out of the rules.
(define keyed.join
  [] -> ""
  [X] -> (str X)
  [X | Xs] -> (@s (str X) "-" (keyed.join Xs)))
(define keyed.encode-slot
  [free] -> fj-free
  [running W E L P] -> (intern (keyed.join [fj run W E L P]))
  [done E P O S] -> (intern (keyed.join [fj done E P O S])))
(define keyed.encode-action
  [expire] -> fj-expire
  [at [T job] Rule] -> (intern (keyed.join [fj T | Rule])))

(define keyed.product
  [] -> [[]]
  [Column | Columns] -> (keyed.extend Column (keyed.product Columns)))
(define keyed.extend
  [] _ -> []
  [X | Xs] Suffixes -> (append (map (/. S [X | S]) Suffixes)
                                 (keyed.extend Xs Suffixes)))
(define keyed.slot-values
  -> [[free] | (append
      (keyed.product [[running] [w1 w2] [e0 e1] [live expired] [pa pb]])
      (keyed.product [[done] [e0 e1] [pa pb] [op0 op1] [sink0 sink1]]))])
(define keyed.at-tenant
  Rules T -> (map (/. R [at [T job] R]) Rules))
(define keyed.action-values
  -> (let Rules (append (keyed.product [[claim] [w1 w2] [pa pb]])
                 (append (keyed.product [[complete] [w1 w2] [e0 e1] [pa pb] [op0 op1]])
                         (keyed.product [[deliver] [pa pb]])))
       [[expire] | (append (keyed.at-tenant Rules a) (keyed.at-tenant Rules b))]))
(define keyed.codec
  Encode Values -> (map (/. V [(Encode V) V]) Values))
(define keyed.codec-start
  -> (do (set *keyed-slots* (keyed.codec (function keyed.encode-slot) (keyed.slot-values)))
         (set *keyed-actions* (keyed.codec (function keyed.encode-action) (keyed.action-values)))))
(define keyed.decode-world
  [fj-pair A B] -> [[[a job] (keyed.find A (value *keyed-slots*))]
                    [[b job] (keyed.find B (value *keyed-slots*))]])
(define keyed.encode-world
  World -> [fj-pair (keyed.encode-slot (keyed.find [a job] World))
                    (keyed.encode-slot (keyed.find [b job] World))])
(define keyed.encode-result
  [next Verdict World] -> [next Verdict (keyed.encode-world World)]
  [unknown Reason] -> [unknown Reason])
(define keyed.next
  Action World ->
    (keyed.encode-result
      (keyed.step (keyed.find Action (value *keyed-actions*)) (keyed.decode-world World))))
