(load "vor.shen")
(load "adapters/shencheck.shen")
(define mapper-test
  Name Actual Expected ->
    (if (= Actual Expected) passed
      (error "~A: expected ~A, got ~A" Name Expected)))
(mapper-test applied
  (shencheck.mapper [sc-observation [tenant-a job-a] payload-a [effect applied]])
  [possibilities [[sc-observation [tenant-a job-a] payload-a [effect applied]]]])
(mapper-test unknown
  (shencheck.mapper [sc-observation [tenant-a job-a] payload-a [effect unknown]])
  [possibilities [[sc-observation [tenant-a job-a] payload-a [effect applied]]
                  [sc-observation [tenant-a job-a] payload-a [effect not-applied]]]])
(mapper-test malformed
  (shencheck.mapper bad) [rejected malformed-observation])
(output "ShenCheck mapper: checks passed.~%")
