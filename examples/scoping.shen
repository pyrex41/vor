\\ Tenant scoping with identifier equality, written once as inert ordinary
\\ Shen definitions (the shape of the FacilityGrid intended-model fragment).
\\ It demonstrates construct/cases.shen and construct/derive-eq.shen:
\\ equality soundness, scoping without hand lemmas, conditional theorems,
\\ conditional contract posts, and generated structural equality.
(tc -)

(define scoping.text
  -> "(define truth.and yes B -> B no B -> no)
      (define truth.pick yes A B -> A no A B -> B)
      (define id.is-one id.one -> yes [id.x0 B] -> no [id.x1 B] -> no)
      (define id.is-x0 id.one -> no [id.x0 B] -> yes [id.x1 B] -> no)
      (define id.is-x1 id.one -> no [id.x0 B] -> no [id.x1 B] -> yes)
      (define id.strip id.one -> id.one [id.x0 B] -> B [id.x1 B] -> B)
      (define id.eq
        id.one Y -> (id.is-one Y)
        [id.x0 A] Y -> (truth.and (id.is-x0 Y) (id.eq A (id.strip Y)))
        [id.x1 A] Y -> (truth.and (id.is-x1 Y) (id.eq A (id.strip Y))))
      (define company-id.raw [company I] -> I)
      (define company-id.eq [company I] C -> (id.eq I (company-id.raw C)))
      (define project-id.raw [project I] -> I)
      (define project-id.eq [project I] P -> (id.eq I (project-id.raw P)))
      (define project-row.id [project-row.mk I C A] -> I)
      (define project-row.company [project-row.mk I C A] -> C)
      (define project-row.archived [project-row.mk I C A] -> A)
      (define project-row.pick yes A B -> A no A B -> B)
      (define projects.find
        projects.nil C P -> project-row.none
        [projects.cons R T] C P ->
          (project-row.pick
            (truth.and (company-id.eq (project-row.company R) C)
                       (project-id.eq (project-row.id R) P))
            [project-row.some R]
            (projects.find T C P)))
      (define project-row.in-company
        project-row.none C -> yes
        [project-row.some R] C -> (company-id.eq (project-row.company R) C))")

(define scoping.source -> (scoping.source-of (scoping.text)))
(define scoping.source-of Text -> [shen-source 0 (read-from-string Text)])
(define scoping.data
  -> [[data truth [[yes []] [no []]]]
      [data id [[id.one []] [id.x0 [id]] [id.x1 [id]]]]
      [data company-id [[company [id]]]]
      [data project-id [[project [id]]]]
      [data project-row [[project-row.mk [project-id company-id truth]]]]
      [data opt-project-row [[project-row.none []] [project-row.some [project-row]]]]
      [data project-table [[projects.nil []] [projects.cons [project-row project-table]]]]])
(define scoping.contracts
  -> (map (/. C (scoping.top-contract C))
       [[truth.and [truth truth] truth] [truth.pick [truth truth truth] truth]
        [id.is-one [id] truth] [id.is-x0 [id] truth] [id.is-x1 [id] truth]
        [id.strip [id] id] [id.eq [id id] truth]
        [company-id.raw [company-id] id] [company-id.eq [company-id company-id] truth]
        [project-id.raw [project-id] id] [project-id.eq [project-id project-id] truth]
        [project-row.id [project-row] project-id] [project-row.company [project-row] company-id]
        [project-row.archived [project-row] truth]
        [project-row.pick [truth opt-project-row opt-project-row] opt-project-row]
        [projects.find [project-table company-id project-id] opt-project-row]
        [project-row.in-company [opt-project-row company-id] truth]]))
(define scoping.top-contract [Name Ins Out] -> [contract Name Ins Out 0 [top]])
(define scoping.signature-of
  Cs -> [fol-signature 1 [] (vor.contract-functions Cs) [] (scoping.data)])
(define scoping.signature -> (scoping.signature-of (scoping.contracts)))
(define scoping.program-of
  Source -> (scoping.ok (vor.normalize Source)))
(define scoping.ok [ok P] -> P  R -> (simple-error (make-string "scoping: ~S" R)))
(define scoping.program -> (scoping.program-of (scoping.source)))
(define scoping.equations-of
  P Sig Cs -> (scoping.constructed (vor.construct-check P Sig Cs (vor.construct P Sig Cs))))
(define scoping.constructed [constructed Eqs] -> Eqs  R -> (simple-error (make-string "scoping: ~S" R)))

\\ ---- theorems ------------------------------------------------------------------
(define scoping.sound
  Sort Eq -> [forall Sort [forall Sort
                [imp [equal truth [app Eq [[v 1] [v 0]]] [app yes []]]
                     [equal Sort [v 1] [v 0]]]]])
(define scoping.scope
  -> [forall company-id [forall project-id [forall project-table
       [equal truth [app project-row.in-company [[app projects.find [[v 0] [v 2] [v 1]]] [v 2]]]
                    [app yes []]]]]])
\\ find(T,C,P) = some(R) -> company(R) = C.   T = v3, C = v2, P = v1, R = v0.
(define scoping.only-company
  -> [forall project-table [forall company-id [forall project-id [forall project-row
       [imp [equal opt-project-row [app projects.find [[v 3] [v 2] [v 1]]] [app project-row.some [[v 0]]]]
            [equal company-id [app project-row.company [[v 0]]] [v 2]]]]]]])
\\ Both checks yes -> the row at the head of the table is returned.
(define scoping.conditional
  Concl -> [forall project-table [forall company-id [forall project-id [forall project-row
       [imp [equal truth [app company-id.eq [[app project-row.company [[v 0]]] [v 2]]] [app yes []]]
         [imp [equal truth [app project-id.eq [[app project-row.id [[v 0]]] [v 1]]] [app yes []]]
              [equal opt-project-row
                [app projects.find [[app projects.cons [[v 0] [v 3]]] [v 2] [v 1]]] Concl]]]]]]])

(define scoping.sound-proof
  Sig Eqs -> (vor.prove-script Sig [] Eqs (scoping.sound id id.eq) [induct induct] 200))
(define scoping.scope-proof
  Sig Eqs -> (vor.prove-script Sig [] Eqs (scoping.scope) [gen gen induct] 200))

\\ Lemmas proved and introduced in order; nothing is assumed.
(define scoping.lemmas
  -> [[(scoping.sound id id.eq) [induct induct]]
      [(scoping.sound company-id company-id.eq) [induct induct]]
      [(scoping.scope) [gen gen induct]]])
(define scoping.chain
  Sig G [] Proof -> (Proof Sig G)
  Sig G [[L S] | Ls] Proof ->
    [apply L [intro (scoping.chain Sig [L | G] Ls Proof)]
       (vor.prove-script Sig [] G L S 200)])
\\ In context [H Scope CSound ISound | Eqs]: Scope at (C,P,T), substitute H,
\\ unfold in-company(some R, C) once, then apply company-id soundness.
(define scoping.only-company-step
  Sig G ->
    (let SomeR [app project-row.some [[v 0]]]
         S0 (vor.proof-specialize (scoping.scope) [[v 2] [v 1] [v 3]] [hyp 1])
         S1 [subst opt-project-row
              [equal truth [app project-row.in-company [[v 0] [v 3]]] [app yes []]]
              [app projects.find [[v 3] [v 2] [v 1]]] SomeR [hyp 0] S0]
         InSome [app project-row.in-company [SomeR [v 2]]]
         Step (vor.eq-rewrite InSome G 0)
         S2 [trans InSome [sym (vor.cases-renumber (scoping.step-proof Step) 1)] S1]
         Spec (vor.proof-specialize (scoping.sound company-id company-id.eq)
                [[app project-row.company [[v 0]]] [v 2]] [hyp 2])
      [gen [gen [gen [gen [intro
        [apply [equal truth (scoping.step-term Step) [app yes []]] Spec S2]]]]]]))
(define scoping.step-term [rewritten T _] -> T  _ -> [app missing []])
(define scoping.step-proof [rewritten _ E] -> E  _ -> [search-failed])
(define scoping.only-company-proof
  Sig Eqs -> (scoping.chain Sig Eqs (scoping.lemmas) (function scoping.only-company-step)))

(define scoping.theorem
  P Theorem Proof ->
    (let Sig (scoping.signature) Cs (scoping.contracts)
      (vor.check-constructed-theorem P Sig Cs (vor.construct P Sig Cs) Theorem Proof 65535)))

\\ ---- negative controls -------------------------------------------------------------
(define scoping.replace-definition
  Name Text [shen-source 0 Ds] ->
    [shen-source 0 (map (/. D (if (= (hd (tl D)) Name) (hd (read-from-string Text)) D)) Ds)])
\\ An id.eq that answers yes for every pair: total, reflexive, and still
\\ "scoped" by the T2-style statement, but not sound.
(define scoping.always-yes
  -> (scoping.program-of (scoping.replace-definition id.eq
       "(define id.eq id.one Y -> yes [id.x0 A] Y -> yes [id.x1 A] Y -> yes)" (scoping.source))))
\\ projects.find without its company check.
(define scoping.no-company-check
  -> (scoping.program-of (scoping.replace-definition projects.find
       "(define projects.find
          projects.nil C P -> project-row.none
          [projects.cons R T] C P ->
            (project-row.pick (truth.and yes (project-id.eq (project-row.id R) P))
              [project-row.some R] (projects.find T C P)))" (scoping.source))))

\\ ---- conditional contract posts (R05 admission) ---------------------------------
\\ truth.pick: J = yes -> pick(J,A,B) = A.  Post scope [Result J A B].
(define scoping.pick-contracts
  Post -> (map (/. C (if (= (hd (tl C)) truth.pick) [contract truth.pick [truth truth truth] truth 0 Post] C))
             (scoping.contracts)))
(define scoping.pick-post-good
  -> [imp [equal truth [v 1] [app yes []]] [equal truth [v 0] [v 2]]])
(define scoping.pick-post-wrong
  -> [imp [equal truth [v 1] [app yes []]] [equal truth [v 0] [v 3]]])
(define scoping.admit-with
  P Cs ->
    (let Sig (scoping.signature-of Cs)
         Con (vor.construct P Sig Cs)
         Eqs (vor.construct-check P Sig Cs Con)
      (vor.admit P Sig Cs
        [vor-admission 0 P Sig Cs Con (map (/. C (scoping.post Sig (scoping.eqs Eqs) C)) Cs)] 65535)))
(define scoping.eqs [constructed Eqs] -> Eqs  _ -> [])
(define scoping.post
  Sig Eqs C -> [post (hd (tl C)) (vor.prove-script Sig [] Eqs (vor.contract-theorem C) [] 200)])

\\ ---- derived structural equality --------------------------------------------------
(define scoping.derived
  -> (vor.derive-eq (scoping.data) [truth yes no]
       [truth id company-id project-id project-row opt-project-row project-table]))
(define scoping.derived-parts [derived-eq Defs Cs Ls] -> [Defs Cs Ls])
(define scoping.derived-program
  Defs -> (scoping.program-of [shen-source 0 Defs]))
(define scoping.derived-signature
  Cs -> [fol-signature 1 [] (vor.contract-functions Cs) [] (scoping.data)])
(define scoping.derived-lemma
  P Cs Ls K ->
    (let Sig (scoping.derived-signature Cs)
         Con (vor.construct P Sig Cs)
         Eqs (scoping.constructed (vor.construct-check P Sig Cs Con))
      (vor.check-constructed-theorem P Sig Cs Con (hd (nth (+ K 1) Ls))
        (vor.derive-lemma-proof Sig Eqs Ls K 200 8) 65535)))
(define scoping.derived-admit
  P Cs -> (let Sig (scoping.derived-signature Cs)
    (vor.admit P Sig Cs [vor-admission 0 P Sig Cs (vor.construct P Sig Cs) (vor.derive-top-posts Cs)] 65535)))

\\ ---- report --------------------------------------------------------------------------
(define scoping.line Label R -> (output "~A: ~S~%" Label R))
(define scoping.run
  -> (let P (scoping.program) Sig (scoping.signature)
          Eqs (scoping.equations-of P Sig (scoping.contracts))
          Y (scoping.always-yes) YEqs (scoping.equations-of Y Sig (scoping.contracts))
          M (scoping.no-company-check) MEqs (scoping.equations-of M Sig (scoping.contracts))
          _ (scoping.line "id.eq sound" (scoping.theorem P (scoping.sound id id.eq) (scoping.sound-proof Sig Eqs)))
          _ (scoping.line "scoping, no hand lemmas" (scoping.theorem P (scoping.scope) (scoping.scope-proof Sig Eqs)))
          _ (scoping.line "find = some(R) -> company(R) = C"
              (scoping.theorem P (scoping.only-company) (scoping.only-company-proof Sig Eqs)))
          _ (scoping.line "always-yes id.eq: soundness"
              (scoping.theorem Y (scoping.sound id id.eq) (scoping.sound-proof Sig YEqs)))
          _ (scoping.line "always-yes id.eq: find = some(R) -> company(R) = C"
              (scoping.theorem Y (scoping.only-company) (scoping.only-company-proof Sig YEqs)))
          _ (scoping.line "no company check: find = some(R) -> company(R) = C"
              (scoping.theorem M (scoping.only-company) (scoping.only-company-proof Sig MEqs)))
          _ (scoping.line "conditional contract post: pick(yes,A,B)=A"
              (scoping.admit-with P (scoping.pick-contracts (scoping.pick-post-good))))
          Parts (scoping.derived-parts (scoping.derived))
          Cs (nth 2 Parts) Ls (nth 3 Parts)
          DP (scoping.derived-program (hd Parts))
          _ (scoping.line "derived equality: admit" (scoping.derived-admit DP Cs))
          _ (scoping.line "derived equality: lemmas"
              (map (/. K (scoping.derived-lemma DP Cs Ls K)) (scoping.range 0 (length Ls))))
       done))
(define scoping.range
  I N -> [] where (>= I N)
  I N -> [I | (scoping.range (+ I 1) N)])
