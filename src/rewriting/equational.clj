(ns rewriting.equational
  "Rewriting system to aid with visibility and debugging of proofs. NOT an automatic theorem prover, just a rewriting tool + proof validation")

(defn qvar? [x]
  "A la PAIP"
  (and (symbol? x)
       (= (subs (str x) 0 1) "?")))

(defn ref? [x]
  "Axioms are referenced by keyword"
  (and (keyword? x) x))

(defn lvar? [x]
  "Of the form *L<int> E.G., *L3, *L1"
  (and (symbol? x)
       (> (count (str x)) 2)
       (= (subs (str x) 0 2) "*L")
       (Integer/parseInt (subs (str x) 2))))

(defn get-axiom [axioms axiom]
  "Either get the axiom, or nil"
  (when (ref? axiom)
    (:fact (axiom axioms))))

(defn get-line [proof line]
  "Either get the line of the proof, or nil"
  (when-let [line-num (lvar? line)]
    (:step (nth proof (- line-num 1)))))

(defn get-line-or-axiom [{:keys [axioms proof]} ref]
  "Either retrieve the axiom, or the line of a proof, or nil"
  (or (get-axiom axioms ref) (get-line proof ref)))

(defn subst [old new data]
  "Substitute bindings for new ones"
  (clojure.walk/prewalk-replace {old new} data))

(defn subst-at-point [old new equation location]
  "Substitute bindings for new ones but only from a specific depth"
  (if (empty? location)
    (concat (subst old new equation))
    (vec
     (concat
      (take (first location) equation)
      (vector (subst-at-point old new (nth equation (first location)) (rest location)))
      (take-last (- (count equation) (+ 1 (first location))) equation)
      ))))

(defn add-binding [k v bindings]
  "Add symbolic binding"
  (let [existing-binding (get bindings k)]
    (cond
      (nil? bindings) nil
      (and existing-binding (not= v existing-binding))
      nil
      existing-binding
      bindings
      :otherwise
      (assoc bindings k v))))

(defn unify [s1 s2 bindings]
  "Classic PAIP unification algorithm"
  (cond
    (nil? bindings) nil
    (= s1 s2) bindings
    (and (coll? s1) (coll? s2)) (unify (rest s1) (rest s2) (unify (first s1) (first s2) bindings))
    (and (qvar? s1) (qvar? s2)) (add-binding s2 s1 (add-binding s1 s2 bindings))
    (qvar? s1) (add-binding s1 s2 bindings)
    (qvar? s2) (add-binding s2 s1 bindings)
    :otherwise nil))

;; (unify '[or [elem ?e ?S1] [elem ?e ?S2]] '[or [elem 4 y] [elem 4 x]] {})


(defn dive [equation location]
  "Dive into a term's subterms a la ACL2"
  (if (empty? location)
    (vec equation)
    (dive (nth equation (first location)) (rest location))))

;; (dive '[equal [or [a b]] [a]] (list 1))

(defn assume [sys command]
  "Assume true"
  (let [step (second command)]
    (update sys :proof #(conj % {:command command
                                 :step step}))))

(defn specify [sys command]
  "Specify bindings for a line or axiom"
  (let [equation (get-line-or-axiom sys (second command))
        bindings (nth command 2)]
    (update sys :proof #(conj % {:command command
                                 :step (reduce (fn [acc [old new]]
                                                 (subst old
                                                        (or (get-line-or-axiom sys new) new)
                                                        acc))
                                               equation
                                               bindings)}))))


(defn fol-or-clauses [{:keys [proof axioms]} clauses]
  "Is there at least one clause that is true"
  (some (fn [clause] ((clojure.set/union
                      (set proof)
                      (set (map :fact (vals axioms))))
                     clause)) clauses))

(defn fol-eval [sys command]
  "Evaluate simple logical equations in line or axiom"
  (let [dive-point (nth command 2)
        equation (dive (get-line-or-axiom sys (second command)) dive-point)
        op (first equation)
        clauses (rest equation)]
    (update sys :proof #(conj % {:command command
                                 :step (case op
                                         or
                                         (if fol-or-clauses
                                           equation
                                           'FAIL))}))))


(defn apply-rewrite [lhs rhs old-term]
  "Apply the rewrite rule holistically"
  (when-let [bindings (unify lhs old-term {})]
    (clojure.walk/prewalk-replace bindings rhs)))

(defn rewrite [sys command]
  "Find the subterm, apply the rewrite, slot the new subterm back in"
  (let [[_ lhs rhs] (get-line-or-axiom sys (second command))
        lhs-or-rhs (nth command 2)
        to-rewrite (get-line-or-axiom sys (nth command 3))
        dive-point (nth command 4)
        subterm-old (dive to-rewrite dive-point)
        subterm-new (if (= lhs-or-rhs 'LHS)
                      (apply-rewrite lhs rhs subterm-old)
                      (apply-rewrite rhs lhs subterm-old))]
    
    (update sys :proof #(conj % {:command command
                                 ;; This is going to do it everywhere....
                                 :step (subst-at-point subterm-old subterm-new to-rewrite dive-point)}))))


(defn prove [name equation commands system]
  "Proof dispatch"
  (let [proof-attempt
        (reduce
         (fn [sys command]
           (if (= 'FAIL (:step (last (:proof sys))))
             sys
             (case (first command)
               assume (assume sys command)
               specify (specify sys command)
               fol-eval (fol-eval sys command)
               rewrite (rewrite sys command)
               sys)))
         {:axioms system :proof []}
         commands)]
    (if (= 'FAIL (:step (last (:proof proof-attempt))))
      'FAIL
      (assoc system name {:fact equation :proof (:proof proof-attempt)}))))

;; [equal [or [elem ?e ?S1] [elem ?e ?S2]]
;;  [elem ?e [union ?S1 ?S2]]]
;; [and [or [elem 4 y] [elem 4 x]] 3]

;; (rewrite {:axioms {:a {:fact '[equal
;;                                [or [elem ?e ?s1] [elem ?e ?s2]]
;;                                [elem ?e [union ?s1 ?s2]]]
;;                        :proof :axiom}}
;;           :proof [{:command 'blah
;;                    :step '[and
;;                            [or [elem 4 y] [elem 4 x]]
;;                            [or [elem 4 y] [elem 4 x]]
;;                            3]}]}
;;          ['rewrite :a 'LHS '*L1 (list 1)])

(clojure.pprint/pprint "")
(clojure.pprint/pprint
 (:elem-4-union-x-y
  (prove :elem-4-union-x-y '[elem 4 [union x y]]
         ;; Commands
         [['assume '[not [elem 4 [union x y]]]]
          ['specify :union-defn '{?A 4 ?S1 x ?S2 y}]
          ['fol-eval '*L2 (list 1)]
          ['rewrite '*L2 'LHS '*L3 nil]
          ['contradict '*L4 '*L1]]
         ;; Proof System
         {:3-elem-x
          {:fact '[elem 3 x]
           :proof :axiom}
          :4-elem-y
          {:fact '[elem 4 y]
           :proof :axiom}
          :union-defn
          {:fact '[equal
                   [or [elem ?A ?S1] [elem ?A ?S2]]
                   [elem ?A [union ?S1 ?S2]]]
           :proof :axiom}})))
(clojure.pprint/pprint "")

