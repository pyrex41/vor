\\ Rule labels represent atomic abstract actions, NOT OS thread scheduling.
(define mutex.model
  -> [vor-model 0 [alice bob] [[false false]]
       [[rule alice-enter [neg [var bob]] [[alice [lit true]]]]
        [rule alice-leave [lit true] [[alice [lit false]]]]
        [rule bob-enter [neg [var alice]] [[bob [lit true]]]]
        [rule bob-leave [lit true] [[bob [lit false]]]]]
       [neg [conj [var alice] [var bob]]]])

(define mutex.broken
  -> [vor-model 0 [alice bob] [[false false]]
       [[rule alice-enter [lit true] [[alice [lit true]]]]
        [rule bob-enter [lit true] [[bob [lit true]]]]]
       [neg [conj [var alice] [var bob]]]])
