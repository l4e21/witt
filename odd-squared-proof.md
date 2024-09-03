Example Problem

An integer n is called even if and only if there exists
an integer k such that n=2k.
An integer n is called odd if and only if there exists an integer
k such that n=2k+1.
Theorem: If n is an odd integer, then n2 is an odd integer

Assume n is odd
Substitute in implication rule for odd implies 2k+1
Then by modus ponens n = 2k + 1
n^2 = 4k^2 + 4k + 1
Which is equivalent to 2k(2k + 2) + 1
Which is equiv to n(n + 2) + 1
Which compiles to odd



Rewrite axioms

```
'[equal [even ?n] [equal ?n [* 2 ?k]]]

'[equal [odd ?n] [equal ?n [+ 1 [* 2 ?k]]]]

'[equal [+ ?a ?b] [+ ?b ?a]]

'[equal [+ ?a ?b] [+ (succ ?a) (pred ?b)]]

'[equal [** ?n 2] [* ?n ?n]]

'[equal [even ?n] [odd [+ 1 ?n]]]

'[equal [* [+ ?a ?b] [+ ?c ?d]] [+ [* ?a ?c] [* ?b ?d] [* ?a ?d] [* ?b ?c]]]

'[equal [+ ?a ?b ?c ?c] [+ ?a ?b [* 2 ?c]]]

[equal [even ?n] [even [* ?n ?n]]]

[equal [even ?n] [even [* 2 ?n]]]

[equal [+ ?a ?b ?c] [+ ?a [+ ?b ?c]]]

[equal [even [+ ?a ?b]] [and [even ?a] [even ?b]]]
```

Theorem

```
'[implies [odd n] [odd [** n 2]]]
```

Procecedure

Add '[odd n] to list of 'transient proof' facts
Add '[equal [odd n] [equal n [+ 1 [+ 2 k]]]] to list of 'transient proof' rewrites by holistic substitution
Add '[equal n [+ 1 [+ 2 k]]] to transient proof rewrites by '[odd n]
Add '[equal [** n 2] [* n n]] to transient proof rewrites by specification
Add '[equal [** n 2] [* [+ 1 [* 2 k]] [+ 1 [* 2 k]]]] to transient proof rewrites by substitution everywhere on RHS only
Add '[equal [** n 2] [+ [* 1 1] [* [* 2 k] [* 2 k]] [* 1 [* 2 k]] [* [* 2 k] 1]]]
Add '[equal [** n 2] [+ 1 [* [* 2 k] [* 2 k]] [* 2 k] [* 2 k]]] by holistic substitution of the rule '[equal [* 1 ?a] ?a]
Add new symbol a-123 by '[equal a-123 [* 2 k]] (gensym)
Have [equal [even a-123] [equal a-123 [* 2 k]]]
Have [even a]
Add '[equal [** n 2] [+ 1 [* a a] a a]]
Add '[equal [** n 2] [+ 1 [* a a] [* 2 a]]]

Now we need some way to ask whether the RHS is odd...

Subproof? [odd [+ 1 [* a a] [* 2 a]]]
Have new subproof be [even [+ [* a a] [* 2 a]]] After a couple steps
Have new subproof [equal [even [+ [* a a] [* 2 a]]] [and [even [* a a]] [even [* 2 a]]]]
Have all RHS eval to true

So in our new rewrite system, we will have rewrites that are applied at certain points, determined by equality (Since equality is the only valid way to define rewrite according to the literature)
Implies can also maybe be used as a one-way holistic rewrite
And or work as before (can be evaluated specially)
We need to have subproofs

