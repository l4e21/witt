(ns rewriting.cnf
  "Rewriting system to aid with visibility and debugging of proofs. NOT an automatic theorem prover, just a rewriting tool + proof validation")


(defn qvar? [x]
  (and (symbol? x)
       (= (subs (str x) 0 1) "?")))

(defn ref? [x]
  (and (keyword? x) x))

(defn lvar? [x]
  (and (symbol? x)
       (> (count (str x)) 2)
       (= (subs (str x) 0 2) "L_")
       (Integer/parseInt (subs (str x) 2))))

(defn get-fact [facts x]
  (->> x
       ref?
       (get facts)
       :fact))

(defn get-line [proof x]
  (when-let [line-num (lvar? x)]
    (nth proof (- line-num 1))))

(defn subst [old new data]
  (clojure.walk/prewalk-replace {old new} data))

(defn assm [{:keys [facts proof] :as sys} step]
  (update sys :proof #(conj % step)))

(defn specify [{:keys [facts proof] :as sys} line step]
  (when-let [line (or (get-line proof line)
                      (get-fact facts line))]
    (update sys :proof
            #(conj % (reduce (fn [acc [old new]]
                               (subst old (or
                                           (get-fact facts new)
                                           (get-line proof new)
                                           new)
                                      acc))
                             line
                             step)))))

(defn construct [{:keys [facts proof] :as sys} op clauses]
  (let [clauses (map (fn [clause] (or (get-fact facts clause)
                                     (get-line proof clause)
                                     clause))
                     clauses)]
    (case op
      or (when (some (fn [clause] ((clojure.set/union
                                   (set proof)
                                   (set (map :fact (vals facts))))
                                  clause)) clauses)
           (update sys :proof #(conj % (vec (concat [op] clauses)))))
      )
    ))

(defn modus-ponens [{:keys [facts proof] :as sys} p1 impl]
  (let [[_ from to] (or (get-fact facts impl)
                        (get-line proof impl))
        p1 (or (get-fact facts p1)
               (get-line proof p1))]
    (if (= from p1)
      (update sys :proof #(conj % to))
      nil)))

(defn contradiction [{:keys [facts proof] :as sys} p1 p2]
  (let [p1 (or (get-fact facts p1) (get-line proof p1))
        p2 (or (get-fact facts p2) (get-line proof p2))]
    (when (or (= p1 ['not p2])
              (= p2 ['not p1]))
      (update sys :proof #(conj % ['contradicts p1 p2])))))



(defn prove [facts steps]
  (reduce
   (fn [acc step]
     (apply (first step) (cons acc (rest step))))
   {:facts facts :proof []}
   steps))

(defn pretty-print [name fact]
  (newline)
  (println (str "Name: " name))
  (println (str "Fact: " (:fact fact)))
  (println "Proof: ")
  (map-indexed (fn [idx {:keys [step line]}]
                 (println (str (+ 1 idx) " -- " step))
                 (println line))
               (:proof fact)))

(defn make-system [facts]
  (fn [operation & args]
    (case operation
      list-axioms (mapv second (filter (fn [[_ fact]] (= (:proof fact) :axiom)) facts))
      prove
      (let [name (first args)
            fact (second args)
            proof-attempt (prove facts (nthrest args 2))]
        (if proof-attempt
          (make-system (assoc facts name
                              {:fact fact
                               :proof
                               (mapv (fn [c p]
                                       {:step c
                                        :line p})
                                     (nthrest args 2)
                                     (:proof proof-attempt))}))
          ['FAIL proof-attempt]))
      proof (:proof (get facts (first args)))
      pretty-print (pretty-print (first args) (get facts (first args))))))


(def sys (make-system {:3-elem-x
                       {:fact '[elem 3 x]
                        :proof :axiom}
                       :4-elem-y
                       {:fact '[elem 4 y]
                        :proof :axiom}
                       :union-defn
                       {:fact '[implies
                                [or [elem ?A ?S1] [elem ?A ?S2]]
                                [elem ?A [union ?S1 ?S2]]]
                        :proof :axiom}}))

(sys 'list-axioms)

(def new-sys (sys 'prove :elem-4-union-x-y '[elem 4 [union x y]]
                  [assm '[not [elem 4 [union x y]]]]
                  [specify :union-defn '{?A 4 ?S1 x ?S2 y}]
                  [construct 'or '[[elem 4 x] :4-elem-y]]
                  [modus-ponens 'L_3 'L_2]
                  [contradiction 'L_1 'L_4]))

(new-sys 'proof :elem-4-union-x-y)

(new-sys 'pretty-print :elem-4-union-x-y)

;; Theory is just a list of ever-growing proven facts (they never shrink)
;; Facts have names, derivations (added by the proof function)
;; Whenever prove is called, the return value is a theory with a new fact that includes a derivation.
;; Shall we namespace theories... and have proper module/package management? Maybe at some point


;; (defn axiom->fact [axiom name]
;;   {:name name
;;    :fact axiom
;;    :proof :axiom})


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
