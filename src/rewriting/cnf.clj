(ns rewriting.cnf
  "Rewriting system to aid with visibility and debugging of proofs. NOT an automatic theorem prover, just a rewriting tool + proof validation")


(defn qvar? [x]
  (and (symbol? x)
       (= (subs (str x) 0 1) "?")))

(defn lvar? [x]
  (and (symbol? x)
       (= (subs (str x) 0 1) "L")
       (Integer/parseInt (subs (str x) 1)) ))

(defn get-fact [facts x]
  (when-let [lvar (lvar? x)]
    (nth facts (- lvar 1))))

(defn subst [old new data]
  (clojure.walk/prewalk-replace {old new} data))

(defn assm [facts step]
  (conj facts step))

(defn specify [facts line step]
  (when-let [fact (get-fact facts line)]
    (conj facts (reduce (fn [acc [old new]] (subst old (or (get-fact facts new) new) acc))
                        fact
                        step))))

(defn construct [facts op clauses]
  (let [clauses (map (fn [clause] (or (get-fact facts clause) clause)) clauses)]
    (case op
      or (when (some (fn [clause] ((set facts) clause)) clauses)
           (conj facts (vec (concat [op] clauses))))
      )
    ))

(defn modus-ponens [facts p1 impl]
  (let [[_ from to] (get-fact facts impl)
        p1 (get-fact facts p1)]
    (if (= from p1)
      (conj facts to)
      nil)))

(defn contradiction [facts p1 p2]
  (let [p1 (get-fact facts p1)
        p2 (get-fact facts p2)]
    (when (or (= p1 ['not p2])
              (= p2 ['not p1]))
      (conj facts ['contradicts p1 p2]))))

;; (defn pretty-print [facts descriptions]
;;   (let [proof (map (fn [f d] (str f " -- " d))
;;                    facts descriptions)]
;;     (clojure.pprint/pprint (vec proof))
;;     facts))


;; Theory is just a list of ever-growing proven facts (they never shrink)
;; Facts have names, derivations (added by the proof function)
;; Whenever prove is called, the return value is a theory with a new fact that includes a derivation.
;; Shall we namespace theories... and have proper module/package management? Maybe at some point


;; (defn axiom->fact [axiom name]
;;   {:name name
;;    :fact axiom
;;    :proof :axiom})

(defn prove [facts steps]
  (reduce
   (fn [acc step]
     (apply (first step) (cons (vec acc) (rest step))))
   facts
   steps))

(defn make-system [facts]
  (fn [operation & args]
    (case operation
      list-axioms (filterv (fn [f] (= (:proof f) :axiom)) facts)
      prove
      (let [name (first args)
            fact (second args)
            proof-attempt (prove (map :fact facts) (nthrest args 2))]
        (if proof-attempt
          (conj facts
                {:name name
                 :fact fact
                 :proof (nthrest args 2)})
          ['FAIL proof-attempt])))))


(def sys (make-system [{:name "3-elem-x"
                        :fact '[elem 3 x]
                        :proof :axiom}
                       {:name "4-elem-y"
                        :fact '[elem 4 y]
                        :proof :axiom}
                       {:name "union-defn"
                        :fact '[implies
                                [or [elem ?A ?S1] [elem ?A ?S2]]
                                [elem ?A [union ?S1 ?S2]]]
                        :proof :axiom}]))

(sys 'list-axioms)

;; (sys 'prove
;;      '[elem 4 [union x y]]
;;      '[(assm [not [elem 4 [union x y]]])
;;        (specify L3 {?A 4 ?S1 x ?S2 y})
;;        (construct or [[elem 4 x] L2])
;;        (modus-ponens L6 L5)
;;        (contradiction L7 L4)])

(sys 'prove "Elem 4 union x y" '[elem 4 [union x y]]
     [assm '[not [elem 4 [union x y]]]]
     [specify 'L3 '{?A 4 ?S1 x ?S2 y}]
     [construct 'or '[[elem 4 x] L2]]
     [modus-ponens 'L6 'L5]
     [contradiction 'L7 'L4])

;; An integer n is called even if and only if there exists
;; an integer k such that n=2k.
;; An integer n is called odd if and only if there exists an integer
;; k such that n=2k+1.
;; Theorem: If n is an odd integer, then n2 is an odd integer

;; '[= ?A ?A]
;; '[implies [= ?A ?B] [implies ?A ?B]]
;; '[implies [= ?A ?B] [implies ?B ?A]]

;; '[= [+ ?A ?B] [+ ?B ?A]]

;; '[implies [* ?A ?B] [* ?B ?A]]

;; '[= [** ?k 2] [* ?k ?k]]

;; '[= [* 2 2] 4]

;; '[implies [even ?n] [= ?n [* 2 ?k]]]

;; '[implies [odd ?n] [= ?n [+ 1 [* 2 ?k]]]]

;; Assume n is odd
;; Substitute in implication rule for odd implies 2k+1
;; Then by modus ponens n = 2k + 1
;; n^2 = 4k^2 + 4k + 1

;; '[= n [+ 1 [* 2 k]]]

;; (defn add-binding [left right bindings]
;;   (assoc bindings left right))


;; (defn unify
;;   ([s1 s2] (unify s1 s2 {}))
;;   ([s1 s2 bindings]
;;    (cond
;;      (= s1 s2) bindings

;;      (qvar? s1) (add-binding s1 s2 bindings)

;;      (qvar? s2) (add-binding s2 s1 bindings)

;;      (and (seq s1) (seq s2))
     
;;      (unify (rest s1) (rest s2) (unify (first s1) (first s2) bindings))
     
;;      :else nil)))

;; (defn unify-at-point
;;   [s1 s2 position]
;;   (letfn [(reduce-position [p]
;;             (cons (- (first p) 1) (rest p)))
;;           (aux [s1 s2 p]
;;             (cond
;;               (= p []) (unify s1 s2 {})
;;               (= (first p) 0) (aux s1 (first s2) (pop p))
;;               :else (unify-at-point s1 (rest s2) (reduce-position p))))]
;;     (aux s1 s2 (reverse position))))

;; (defn write-proof [system proof-specs])

;; ;; 1. We should probably replace facts list with a system of facts with their own subproofs 
;; (unify [1 2 3] [1 2 '?a])

;; ;; Example of a common rewriting problem
;; '[implies [f ?x] ?x]
;; '[f [f x]]
;; ;; Where do we replace ? How do we know? Need a custom unification that takes the location of the subpattern probably

;; (unify '[f ?x] '[f [f x]])
