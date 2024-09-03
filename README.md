
Equational term-rewriting system to aid with visibility and debugging of proofs. NOT an automatic theorem prover, just a rewriting tool + proof validation

## TODO

- fol-construct command
- induce command (partial ordering)
- composition examples
- strategies
- tests
- change the example to use implication explicitly

## Philosophy

In the Philosophical Investigations, Wittgenstein tells us that it makes no sense to ask 'what the definition' of a concept is, only to give examples. It is with this philosophy in mind that I've produced this 'proof debugger' -- NOT to prove things on its own at all, but simply to allow humans to produce human-readable proofs that the machine will verify, and to thereby produce composable packages of verifiable proofs using equational logic.

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
  - Can eval FOL (and/or/implies)
  - For implication theorems, can make assumptions and prove by contra
  
A subproof may functionally just be 'I am asking this question, can you store this as a thing that I can do rewrites on'. Not sure I actually need subproofs yet! Hopefully not.


## Example

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
