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

(defn get-fn [{:keys [fns]} ref]
  (and (symbol? ref) (ref fns)))

(defn subst [old new data]
  "Substitute bindings for new ones"
  (clojure.walk/postwalk-replace {old new} data))

(defn subst-at-point [old new equation location]
  "Substitute bindings for new ones but only from a specific depth"
  (if (empty? location)
    (subst old new equation)
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
    (and (coll? s1) (coll? s2))
    (cond
      (and (empty? s1) (empty? s2))
      bindings
      :otherwise
      (unify (rest s1) (rest s2) (unify (first s1) (first s2) bindings)))
    (and (qvar? s1) (qvar? s2)) (add-binding s2 s1 (add-binding s1 s2 bindings))
    (qvar? s1) (add-binding s1 s2 bindings)
    (qvar? s2) (add-binding s2 s1 bindings)
    (= s1 s2) bindings
    :otherwise nil))

(defn depth-first-unify [s1 s2 bindings]
  "Left hand static, s2 depth first search for unification..."
  (reduce
   (fn [acc s2-subterm]
     (clojure.pprint/pprint bindings)
     (clojure.pprint/pprint s1)
     (clojure.pprint/pprint s2-subterm)
     (clojure.pprint/pprint (unify s1 s2-subterm {}))
     (if (seq acc)
       acc
       (merge acc (if (coll? s2-subterm)
                    (unify s1 s2-subterm (depth-first-unify s1 s2-subterm acc))
                    nil))))
   bindings
   s2))

;; (unify '[or [elem ?e ?S1] [elem ?e ?S2]] '[or [elem 4 y] [elem 4 x]] {})
(unify '[succ :nat ?n] '[succ :nat ?n] {})
(depth-first-unify '[succ :nat ?n] '[+ [succ :nat ?n] [1 2 [succ :nat ?n]]] {})

(defn dive [equation location]
  "Dive into a term's subterms a la ACL2"
  (if (empty? location)
    (if (coll? equation)
      (vec equation)
      equation)
    (dive (nth equation (first location)) (rest location))))

;; (dive '[equal [or [a b]] [a]] (list 1))

(defn assume [sys command]
  "Assume true"
  (second command))

(defn specify [sys command]
  "Specify bindings for a line or axiom"
  (let [equation (get-line-or-axiom sys (second command))
        bindings (nth command 2)]
    (reduce (fn [acc [old new]]
              (subst old
                     (or (get-line-or-axiom sys new) new)
                     acc))
            equation
            bindings)))

;; This should be replaced with an evaluation and functions should have their own point in the system
(defn evaluate [sys command]
  "Evaluate simple logical equations in line or axiom"
  (let [dive-point (nth command 2)
        equation (dive (get-line-or-axiom sys (second command)) dive-point)
        operation (get-fn sys (first equation))]
    (if operation
      (operation sys equation)
      'FAIL)))


(defn apply-rewrite [lhs rhs old-term]
  "Apply the rewrite rule holistically"
  ;; (clojure.pprint/pprint lhs)
  ;; (clojure.pprint/pprint rhs)
  ;; (clojure.pprint/pprint old-term)

  (when-let [bindings (unify lhs old-term {})]
    (do
      ;; (clojure.pprint/pprint bindings)
      (clojure.walk/prewalk-replace bindings rhs))))

(defn rewrite [sys command]
  "Find the subterm, apply the rewrite, slot the new subterm back in"
  ;; (clojure.pprint/pprint command)
  (let [[_ lhs rhs] (get-line-or-axiom sys (second command))
        lhs-or-rhs (nth command 2)
        to-rewrite (get-line-or-axiom sys (nth command 3))
        dive-point (nth command 4)
        subterm-old (dive to-rewrite dive-point)
        subterm-new (if (= lhs-or-rhs 'LHS)
                      (apply-rewrite lhs rhs subterm-old)
                      (apply-rewrite rhs lhs subterm-old))]

    (if (get-line-or-axiom sys (second command))
      (subst-at-point subterm-old subterm-new to-rewrite dive-point)
      'FAIL)))

(defn construct [sys command]
  "Construct a symbol that represents a term"
  ['equal (second command) (nth command 2)])

(defn prove [name equation commands system]
  "Proof dispatch"
  (let [proof-attempt
        (reduce
         (fn [sys command]
           (if (= 'FAIL (:step (last (:proof sys))))
             sys
             (let [proof-step
                   (case (first command)
                     assume (assume sys command)
                     specify (specify sys command)
                     evaluate (evaluate sys command)
                     rewrite (rewrite sys command)
                     construct (construct sys command)
                     sys)]
               (update sys :proof #(conj % {:command command
                                            :step proof-step})))))
         {:fns (:fns system) :axioms (:facts system) :proof []}
         commands)]
    (if (= 'FAIL (:step (last (:proof proof-attempt))))
      'FAIL
      (update system :facts #(assoc % name {:fact equation :proof (:proof proof-attempt)})))))

(clojure.pprint/pprint "")
;; (clojure.pprint/pprint
;;  (:elem-4-union-x-y
;;   (:facts
;;    (prove :elem-4-union-x-y '[elem 4 [union x y]]
;;           ;; Commands
;;           [['assume '[not [elem 4 [union x y]]]]
;;            ['specify :union-defn '{?A 4 ?S1 x ?S2 y}]
;;            ['evaluate '*L2 (list 1)]
;;            ['rewrite '*L2 'LHS '*L3 nil]
;;            ['contradict '*L4 '*L1]]
;;           ;; Proof System
;;           {:fns
;;            ;; We do have to have some basic evaluator, just because FOL is required as a baseline for all of this work, and maybe the user wants to extend in the future.
;;            {'or (fn [{:keys [axioms fns proof]} equation]
;;                   (if (some (fn [clause] ((clojure.set/union
;;                                           (set proof)
;;                                           (set (map :fact (vals axioms))))
;;                                          clause)) (rest equation))
;;                     equation
;;                     'FAIL))}
;;            :facts
;;            {:3-elem-x
;;             {:fact '[elem 3 x]
;;              :proof :axiom}
;;             :4-elem-y
;;             {:fact '[elem 4 y]
;;              :proof :axiom}
;;             :union-defn
;;             {:fact '[equal
;;                      [or [elem ?A ?S1] [elem ?A ?S2]]
;;                      [elem ?A [union ?S1 ?S2]]]
;;              :proof :axiom}}}))))
(clojure.pprint/pprint "")

;; Let's say we want to prove that the sum of the first n positive integers is equal to (n * (n + 1) / 2
(clojure.pprint/pprint "")
;; (:sum-n-implies-n-plus-1-theorem
;;  (:facts
;;   (prove :sum-n-implies-n-plus-1-theorem '[implies
;;                                            [equal [sum ?n] [/ [* ?n [+ 1 ?n]] 2]]
;;                                            [equal [sum [succ :nat ?n]]
;;                                             [/ [* [succ :nat ?n]
;;                                                 [+ 1 [succ :nat ?n]]]
;;                                              2]]]
;;          ;; show equal to + n [/ [* ?n [+ 1 ?n]] 2]
;;          [['assume '[equal [sum n] [/ [* n [+ 1 n]] 2]]]
;;           ;; Construct intermediate symbol
;;           ['construct 'X '[/ [* [succ :nat ?n]
;;                               [+ 1 [succ :nat ?n]]]
;;                            2]] 
;;           ['rewrite :1-plus-1 'RHS '*L2 nil]
;;           ]
;;          (prove :sum-1-theorem '[equal [sum 1] [/ [* 1 [+ 1 1]] 2]]
;;                 ;; Commands
;;                 [['specify :div-n-n-1 '{?n 2}]
;;                  ['rewrite '*L1 'RHS :sum-1 (list 2)]
;;                  ['rewrite :1-*-n-n 'RHS '*L2 (list 2 1)]
;;                  ['rewrite :order-1-2-succ 'RHS '*L3 (list 2 1 2)]
;;                  ['rewrite :1-plus-1 'RHS '*L4 (list 2 1 2)]
;;                  ]
;;                 {:fns
;;                  {'or (fn [{:keys [axioms fns proof]} equation]
;;                         (if (some (fn [clause] ((clojure.set/union
;;                                                 (set proof)
;;                                                 (set (map :fact (vals axioms))))
;;                                                clause)) (rest equation))
;;                           equation
;;                           'FAIL))}
;;                  :facts
;;                  {:sum-1
;;                   {:fact '[equal [sum 1] 1]
;;                    :proof :axiom}
;;                   :sum
;;                   {:fact '[equal [sum ?a] [+ ?a [sum [pred :nat ?a]]]]
;;                    :proof :axiom}
;;                   :order-1-2-succ
;;                   {:fact '[equal [succ :nat 1] 2]
;;                    :proof :axiom}
;;                   :order-1-2-pred
;;                   {:fact '[equal [pred :nat 2] 1]
;;                    :proof :axiom}
;;                   :order-2-3-succ
;;                   {:fact '[equal [succ :nat 2] 3]
;;                    :proof :axiom}
;;                   :order-2-3-pred
;;                   {:fact '[equal [pred :nat 3] 2]
;;                    :proof :axiom}
;;                   :div-n-n-1
;;                   {:fact '[equal [/ ?n ?n] 1]
;;                    :proof :axiom}
;;                   :1-plus-1
;;                   {:fact '[equal [+ 1 ?n] [succ :nat ?n]]
;;                    :proof :axiom}
;;                   :1-*-n-n
;;                   {:fact '[equal [* 1 ?n] ?n]
;;                    :proof :axiom}
;;                   }}))))
;; (:sum-n-up-to (:facts
;;                (prove :sum-n-up-to '[for :nat [equal [sum ?n] [/ [* ?n [+ 1 ?n]] 2]]]
;;                       ;; Commands
;;                       [['assume '[/ [* ?n [+ 1 ?n]] 2]]
;;                        ['specify '*L1 {'?n 1}]
;;                        ['rewrite :1-plus-1 'LHS '*L2 (list 1 2)]
;;                        ['rewrite :order-1-2-succ 'LHS '*L3 (list 1 2)]
;;                        ['rewrite :1-*-n-n 'LHS '*L4 (list 1)]
;;                        ['rewrite :div-n-n-1 'LHS '*L5 nil]
;;                        ]
;;                       ;; 1 works 
;;                       ;; Proof System
;;                       {:fns
;;                        ;; We do have to have some basic evaluator, just because FOL is required as a baseline for all of this work, and maybe the user wants to extend in the future.
;;                        {'or (fn [{:keys [axioms fns proof]} equation]
;;                               (if (some (fn [clause] ((clojure.set/union
;;                                                       (set proof)
;;                                                       (set (map :fact (vals axioms))))
;;                                                      clause)) (rest equation))
;;                                 equation
;;                                 'FAIL))}
;;                        :facts
;;                        {:sum-1
;;                         {:fact '[equal [sum 1] 1]
;;                          :proof :axiom}
;;                         :sum
;;                         {:fact '[equal [sum ?a] [+ ?a [sum [pred :nat ?a]]]]
;;                          :proof :axiom}
;;                         :order-1-2-succ
;;                         {:fact '[equal [succ :nat 1] 2]
;;                          :proof :axiom}
;;                         :order-1-2-pred
;;                         {:fact '[equal [pred :nat 2] 1]
;;                          :proof :axiom}
;;                         :order-2-3-succ
;;                         {:fact '[equal [succ :nat 2] 3]
;;                          :proof :axiom}
;;                         :order-2-3-pred
;;                         {:fact '[equal [pred :nat 3] 2]
;;                          :proof :axiom}
;;                         :div-n-n-1
;;                         {:fact '[equal [/ ?n ?n] 1]
;;                          :proof :axiom}
;;                         :1-plus-1
;;                         {:fact '[equal [+ 1 ?n] [succ :nat ?n]]
;;                          :proof :axiom}
;;                         :1-*-n-n
;;                         {:fact '[equal [* 1 ?n] ?n]
;;                          :proof :axiom}
;;                         }})))

(clojure.pprint/pprint "")
