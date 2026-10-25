\\ Trusted fenced-job service policy. Requests are inert VOR-DATA values;
\\ no request chooses a Shen function, model, or source.
(load "adapters/fenced-profile.shen")
(load "adapters/history-producer.shen")
(load "adapters/shencheck.shen")
(load "adapters/history-checker.shen")

(define fj.job-symbols ->
  [fj-start fj-observe fj-packed fj-history fj-op fj-effect fj-evidence fj-dag fj-final fj-snapshot
   fj-node fj-edge applied not-applied unknown allow deny produced rejected next
   accepted total-admission malformed-history invalid-budget node-budget
   transition-budget producer-only malformed-certificate checked violation
   impossible-observation bad-terminal unresolved-observation mixed-terminal-outcomes
   fj-free fj-pair fj-run-w1-e0-live-pa fj-run-w1-e0-live-pb
   fj-run-w1-e0-expired-pa fj-run-w1-e0-expired-pb fj-run-w1-e1-live-pa
   fj-run-w1-e1-live-pb fj-run-w1-e1-expired-pa fj-run-w1-e1-expired-pb
   fj-run-w2-e0-live-pa fj-run-w2-e0-live-pb fj-run-w2-e0-expired-pa
   fj-run-w2-e0-expired-pb fj-run-w2-e1-live-pa fj-run-w2-e1-live-pb
   fj-run-w2-e1-expired-pa fj-run-w2-e1-expired-pb fj-done-e0-pa-op0-sink0
   fj-done-e0-pa-op0-sink1 fj-done-e0-pa-op1-sink0 fj-done-e0-pa-op1-sink1
   fj-done-e0-pb-op0-sink0 fj-done-e0-pb-op0-sink1 fj-done-e0-pb-op1-sink0
   fj-done-e0-pb-op1-sink1 fj-done-e1-pa-op0-sink0 fj-done-e1-pa-op0-sink1
   fj-done-e1-pa-op1-sink0 fj-done-e1-pa-op1-sink1 fj-done-e1-pb-op0-sink0
   fj-done-e1-pb-op0-sink1 fj-done-e1-pb-op1-sink0 fj-done-e1-pb-op1-sink1
   fj-a-claim-w1-pa fj-a-claim-w1-pb fj-a-claim-w2-pa fj-a-claim-w2-pb
   fj-a-complete-w1-e0-pa-op0 fj-a-complete-w1-e0-pa-op1
   fj-a-complete-w1-e1-pa-op0 fj-a-complete-w1-e1-pa-op1
   fj-a-complete-w1-e0-pb-op0 fj-a-complete-w1-e0-pb-op1
   fj-a-complete-w1-e1-pb-op0 fj-a-complete-w1-e1-pb-op1
   fj-a-complete-w2-e0-pa-op0 fj-a-complete-w2-e0-pa-op1
   fj-a-complete-w2-e0-pb-op0 fj-a-complete-w2-e0-pb-op1
   fj-a-complete-w2-e1-pa-op0 fj-a-complete-w2-e1-pa-op1
   fj-a-complete-w2-e1-pb-op0 fj-a-complete-w2-e1-pb-op1
   fj-a-deliver-pa fj-a-deliver-pb fj-b-claim-w1-pa fj-b-claim-w1-pb
   fj-b-claim-w2-pa fj-b-claim-w2-pb fj-b-complete-w1-e0-pa-op0
   fj-b-complete-w1-e0-pa-op1 fj-b-complete-w1-e0-pb-op0
   fj-b-complete-w1-e0-pb-op1 fj-b-complete-w1-e1-pa-op0
   fj-b-complete-w1-e1-pa-op1 fj-b-complete-w1-e1-pb-op0
   fj-b-complete-w1-e1-pb-op1 fj-b-complete-w2-e0-pa-op0
   fj-b-complete-w2-e0-pa-op1 fj-b-complete-w2-e0-pb-op0
   fj-b-complete-w2-e0-pb-op1 fj-b-complete-w2-e1-pa-op0
   fj-b-complete-w2-e1-pa-op1 fj-b-complete-w2-e1-pb-op0
   fj-b-complete-w2-e1-pb-op1 fj-b-deliver-pa fj-b-deliver-pb fj-expire])

(define fj.job-decode
  Bytes -> (vor.unpack-known Bytes 262144 128 65536 (fj.job-symbols)))
(define fj.job-pack
  Value -> (vor.pack Value 262144 128 65536))
(define fj.job-produced
  [produced Evidence] -> Evidence
  _ -> missing)
(define fj.job-request
  [fj-start History] ->
    (let P (fj.job-produced (fj.produce History 512 100000))
      (if (= P missing) [unknown producer-only]
        (fj.job-start-packed (fj.job-pack P))))
  [fj-observe [fj-packed Bytes]] ->
    (fj.job-observe-packed (fj.job-decode Bytes))
  [fj-observe Evidence] -> (fj.check-history Evidence)
  _ -> [rejected malformed-request])
(define fj.job-pack-result
  [ok Bytes] -> [produced Bytes]
  [rejected Reason] -> [unknown producer-only]
  [unknown Reason] -> [unknown producer-only]
  _ -> [unknown producer-only])
(define fj.job-start-packed
  [ok _] -> [unknown producer-only]
  _ -> [unknown producer-only])
(define fj.job-observe-packed
  [ok Evidence] -> (fj.check-history Evidence)
  [unknown Reason] -> [unknown Reason]
  [rejected Reason] -> [rejected Reason]
  _ -> [rejected malformed-evidence])
(define vor.async.check
  Bytes -> (fj.job-observe-bytes Bytes))
(define vor.async.produce
  Bytes -> (fj.job-produce-bytes Bytes))
(define fj.job-produce-bytes
  Bytes -> (fj.job-produce-decode (fj.job-decode Bytes)))
(define fj.job-produce-decode
  [ok History] -> (fj.job-pack-result (fj.job-pack-result-value (fj.produce History 512 100000)))
  [unknown Reason] -> [unknown Reason]
  [rejected Reason] -> [rejected Reason]
  _ -> [rejected malformed-history])
(define fj.job-pack-result-value
  [produced Evidence] -> (fj.job-pack Evidence)
  [unknown Reason] -> [unknown Reason]
  [rejected Reason] -> [rejected Reason]
  _ -> [unknown producer-only])
(define fj.job-observe-bytes
  Bytes -> (fj.job-observe-decode (fj.job-decode Bytes)))
(define fj.job-observe-decode
  [ok Evidence] -> (fj.check-history Evidence)
  [unknown Reason] -> [unknown Reason]
  [rejected Reason] -> [rejected Reason]
  _ -> [rejected malformed-evidence])
(define fj.job-request-result
  [ok Request] -> (fj.job-request Request)
  [unknown Reason] -> [unknown Reason]
  [rejected Reason] -> [rejected Reason]
  _ -> [rejected malformed-request])

(let Startup (fj.session-start)
  (if (= Startup [accepted total-admission]) true
      (simple-error "fenced profile admission failed")))
