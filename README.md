
Equational term-rewriting system to aid with visibility and debugging of proofs. NOT an automatic theorem prover, just a rewriting tool for pedagogical proof validation

## TODO

- more composition examples
- tests
- multivariable looping + more abstract intense induction examples
- multiparameter commutativity

## Philosophy

In the Philosophical Investigations, Wittgenstein tells us that it makes no sense to ask 'what the definition' of a concept is, only to give examples. It is with this philosophy in mind that I've produced this 'proof debugger' -- NOT to prove things on its own at all, but simply to allow humans to produce human-readable proofs that the machine will verify, and to thereby produce composable packages of verifiable proofs using equational logic.

Underpinning this undertaking is the fundamental idea that process is more important than outcome. This won't help you prove your programs. It's a purely pedagogical mathematics tool.

Induction is implemented purely relationally. Arbitrary relations connect the base to a given value, that can be passed into the quantification for the induction rule. Dependent types implicitly and naturally fall out of this. 

## Literature

'Term Rewriting and All That'

'Computer Aided Reasoning - An Approach'

'Automated Reasoning about Set-Point Topology'

## Implementation

Main file is `equational.clj`

Proof System is just a list of facts

Each fact has
  1. an equation
  2. a name
  3. Its own proof

Each proof is a list of transient fact-results with each associated command
Proof probably also needs to contain info about strategy, documentation, etc

Commands:
  - Reference statements like *L1 *L2
  - Reference axioms by name (keywords are reserved for axioms)
  - Can be holistic or otherwise substitution/unification
  - Can eval user-given native clojure fns
  - For implication theorems, can make assumptions and prove by contra
  - Can perform multivariable induction
  

## Simple Example

We might have the following proof system

```
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
  :proof :axiom}}
  ```

And we might try to `prove` that 4 is an element of the union by contradiction using commands

['assm '[not [elem 4 [union x y]]]]  -- valid since we can assume anything

['specify :union-defn {?A 4 ?S1 y ?S2 x}]  -- valid since we can specify anything holistically

['fol-eval *L2 (list 1)]  -- valid since we can naively eval simple FOL statements.

['rewrite *L2 'LHS *L3 nil]  -- The famous Modus Ponens relation

['contradict *L4 *L1] -- The theorem is contradicted

This should work just fine and deliver us the new fact

```clojure
{:fact [elem 4 [union x y]],
 :proof
 [{:command [assume [not [elem 4 [union x y]]]],
   :step [not [elem 4 [union x y]]]}
  {:command [specify :union-defn {?A 4, ?S1 x, ?S2 y}],
   :step [equal [or [elem 4 x] [elem 4 y]] [elem 4 [union x y]]]}
  {:command [fol-eval *L2 (1)], :step [or [elem 4 x] [elem 4 y]]}
  {:command [rewrite *L2 LHS *L3 nil], :step (elem 4 [union x y])}]}
```


## More complex example
 
Suppose we want to prove that the sum of the first n natural numbers is equal to `(n * (n + 1)) / 2`.

We can prove this via induction. We can prove the base case as follows.

```
'[equal [sum 1] [/ [* 1 [+ 1 1]] 2]]
```

```
['specify :div-n-n-1 '{?n 2}]
['rewrite '*L1 'RHS :sum-1 (list 2)]
['rewrite :1-*-n-n 'RHS '*L2 (list 2 1)]
['rewrite :order-1-2-succ 'RHS '*L3 (list 2 1 2)]
['rewrite :1-plus-1 'RHS '*L4 (list 2 1 2)]
          ```

In a few cases, rewrites have to be rather ugly because so far we don't have arbitrary commutativity and associativity rules for addition... perhaps we might prove *this* via induction in the future!

```
{:fact [equal [sum 1] [/ [* 1 [+ 1 1]] 2]],
 :proof
 [{:command [specify :div-n-n-1 {?n 2}], :step [equal [/ 2 2] 1]}
  {:command [rewrite *L1 RHS :sum-1 (2)],
   :step [equal [sum 1] [/ 2 2]]}
  {:command [rewrite :1-*-n-n RHS *L2 (2 1)],
   :step [equal [sum 1] [/ [* 1 2] 2]]}
  {:command [rewrite :order-1-2-succ RHS *L3 (2 1 2)],
   :step [equal [sum 1] [/ [* 1 [succ :nat 1]] 2]]}
  {:command [rewrite :1-plus-1 RHS *L4 (2 1 2)],
   :step [equal [sum 1] [/ [* 1 [+ 1 1]] 2]]}]}
```

Great. Now for the inductive case.

```
[implies
  [equal [sum ?n] [/ [* ?n [+ 1 ?n]] 2]]
  [equal
   [sum [succ :nat ?n]]
   [/ [* [succ :nat ?n] [+ 1 [succ :nat ?n]]] 2]]]
```

```
['assume '[equal [sum n] [/ [* n [+ 1 n]] 2]]]
;; Construct intermediate symbol
['construct 'X '[/ [* [succ :nat n] [+ 1 [succ :nat n]]] 2]]
;; Rewrite succ n to n + 1 in the formula
['rewrite :1-plus-1 'RHS '*L2 nil]
;; Quadratic-expansion axiom given
['rewrite :quadratic-expansion 'LHS '*L3 nil]
['rewrite :commutativity-of-* 'LHS '*L4 (list 2 1 3)]
;; We can only rewrite this for one var at a time right now. Future optimisation.
['rewrite :1-*-n-n 'LHS '*L5 nil]
['rewrite :1-*-n-n 'LHS '*L6 nil]
['rewrite :1-*-n-n 'LHS '*L7 nil]
['rewrite :addition-expansion 'LHS '*L8 nil]
['rewrite :division-by-two 'LHS '*L9 nil]
['rewrite '*L1 'RHS '*L10 (list 2 2)]
['rewrite '*L2 'LHS '*L11 nil]
['rewrite :sum-fact-def 'LHS '*L12 nil]
['rewrite :commutativity-of-equal 'LHS '*L13 nil]
```

```
{:fact
 [implies
  [equal [sum ?n] [/ [* ?n [+ 1 ?n]] 2]]
  [equal
   [sum [succ :nat ?n]]
   [/ [* [succ :nat ?n] [+ 1 [succ :nat ?n]]] 2]]],
 :proof
 [{:command [assume [equal [sum n] [/ [* n [+ 1 n]] 2]]],
   :step [equal [sum n] [/ [* n [+ 1 n]] 2]]}
  {:command [construct X [/ [* [succ :nat n] [+ 1 [succ :nat n]]] 2]],
   :step [equal X [/ [* [succ :nat n] [+ 1 [succ :nat n]]] 2]]}
  {:command [rewrite :1-plus-1 RHS *L2 nil],
   :step [equal X [/ [* [+ 1 n] [+ 1 [+ 1 n]]] 2]]}
  {:command [rewrite :quadratic-expansion LHS *L3 nil],
   :step
   [equal X [/ [+ [* 1 1] [* 1 [+ 1 n]] [* n 1] [* n [+ 1 n]]] 2]]}
  {:command [rewrite :commutativity-of-* LHS *L4 (2 1 3)],
   :step
   [equal X [/ [+ [* 1 1] [* 1 [+ 1 n]] [* 1 n] [* n [+ 1 n]]] 2]]}
  {:command [rewrite :1-*-n-n LHS *L5 nil],
   :step [equal X [/ [+ 1 [* 1 [+ 1 n]] [* 1 n] [* n [+ 1 n]]] 2]]}
  {:command [rewrite :1-*-n-n LHS *L6 nil],
   :step [equal X [/ [+ 1 [+ 1 n] [* 1 n] [* n [+ 1 n]]] 2]]}
  {:command [rewrite :1-*-n-n LHS *L7 nil],
   :step [equal X [/ [+ 1 [+ 1 n] n [* n [+ 1 n]]] 2]]}
  {:command [rewrite :addition-expansion LHS *L8 nil],
   :step [equal X [/ [+ [* 2 1] [* 2 n] [* n [+ 1 n]]] 2]]}
  {:command [rewrite :division-by-two LHS *L9 nil],
   :step [equal X [+ [+ 1 n] [/ [* n [+ 1 n]] 2]]]}
  {:command [rewrite *L1 RHS *L10 (2 2)],
   :step [equal X [+ [+ 1 n] [sum n]]]}
  {:command [rewrite *L2 LHS *L11 nil],
   :step
   [equal
    [/ [* [succ :nat n] [+ 1 [succ :nat n]]] 2]
    [+ [+ 1 n] [sum n]]]}
  {:command [rewrite :sum-fact-def LHS *L12 nil],
   :step
   [equal
    [/ [* [succ :nat n] [+ 1 [succ :nat n]]] 2]
    [sum [succ :nat n]]]}
  {:command [rewrite :commutativity-of-equal LHS *L13 nil],
   :step
   [equal
    [sum [succ :nat n]]
    [/ [* [succ :nat n] [+ 1 [succ :nat n]]] 2]]}]}
```

A long-ish result, but much much shorter than anything you'll get out of ACL2!

Now the fun part. We have our base & inductive cases, so all we need to do now is construct the inductive assertion.

```
'[forall {?n 1} {?n [succ :nat ?n]} [equal [sum ?n] [/ [* ?n [+ 1 ?n]] 2]]]             
```


```
[['induce '{?n 1} '{?n [succ :nat ?n]} '[equal [sum ?n] [/ [* ?n [+ 1 ?n]] 2]]]]         
```

We allow the user to pass in an ordered map (currently unordered, but when we reify multivariables it will be ordered) so that we can have complex quantification rules. The first map is the base-case bindings. The second is the bindings for the delta function, and the third arg is the theorem. 

The `induce` command finds the base-case in the facts list by adding the bindings from the first map to the theorem, constructs the inductive case from adding the bindings from the second map to the theorem and turning this into an `implies` statement, and then finds that in the facts list. If all of this works, the inductive rule is proven for all of the natural numbers greater than 1! The constraint and beauty here lies in the fact that this is all done via a relational graph. Theoretically, your inductive step could be **any relation**. This is extremely powerful because it means you have a highly flexible dependent type system that is implicit.

How do we apply this rule, then? What happens behind the scenes? This is the most interesting part.

Say we want to prove 

```
'[equal [sum 3] [/ [* 3 4] 2]]
```

We can apply the induction using `apply-induction`.

```
['apply-induction :induction-sum '{?n 3}]
```

This takes a map of bindings and the inductive rule, and from the base-case, searches using the inductive rule's step-function in order to check whether the base is connected to the value by that step-function. If so, by definition the induction **must** apply. Amazingly simple and yields a very simple one-line proof.


```
{:fact [equal [sum 3] [/ [* 3 4] 2]],
 :proof
 [{:command [apply-induction :induction-sum {?n 3}],
   :step [equal [sum 3] [/ [* 3 [+ 1 3]] 2]]}]}
```


