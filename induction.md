
### Induction

In order to implement well-founded induction, we require partial ordering. And for partial ordering, we may need a type system. But I would like this type system to be dynamic and extensible, and preferably relationally-driven. 

Our system has as of right now just a map of facts. I would prefer not to implement types unless I see the need as the work unfurls-- therefore, I will start simply by adding partial orders. And if we are doing it this way, we don't necessarily need anything other than facts. So maybe we do not need any kind of special handling other than a dispatch for an `order` fn.

There are two diverging paths our system could go for with trade-offs.

1. We can implement orders as their own thing, with clojure dispatch functions. This creates some opaqueness in our system, but improves computing power. 

E.G., we have a command

['add-order :nat (fn [a b] (and (integerp a) (integerp b) (> a 0) (> b 0) (< a b)))]

And we would then use this order when we call `induct`

But is there a way to do it... without the lambdas, so that we can still have our relations? Well. Let's see.

Suppose instead we have 

['add-order :nat '[and [clojure.core/integer? ?a] [clojure.core/integer? ?b] [clojure.core/< ?a ?b]]]

Producing

'[order :nat '[and [clojure.core/integer? ?a] [clojure.core/integer? ?b] [clojure.core/< ?a ?b]]]


Now, we definitely need some eval dispatch for this. I'm also still not very happy about this because it might tamper with other parts of the system if it's in with the other facts. But we can try it.

So how will `evaluate` work in this case? Well we need some notion of a `define`. 

['define 'and '[a b c] ['clojure.core/and 'a 'b 'c]]

And when `evaluate` is called it will expand

So let's say we evaluate our nat ordering

'[and [clojure.core/integer? ?a] [clojure.core/integer? ?b] [clojure.core/< ?a ?b]]

becomes 

'[clojure.core/and [clojure.core/integer? ?a] [clojure.core/integer? ?b] [clojure.core/< ?a ?b]] because first it looks everything up depth-first and unifies and substitutes and blah blah. Now when everything's done it should just evaluate in an evaluator. This way we can evaluate things when we want to and then add an `equal` at the end. That's okay I guess. Are there edge cases? Well, what if parts aren't unified? Then we can just partially evaluate them maybe?



2. We can eschew types entirely, keeping everything relational, forcing the user to define explicitly the orders they care about. This keeps things highly transparent. This seems tedious, and it is computationally more intensive and slower as well as not handling all numbers, but there are methods to make this easier for the user. E.G.,

E.G.,

['add-order-fact 'nat-order '1 '2]

Would add
'[nat-order 1 2] to our list of facts.

Then our induction would prove for a 'base case' by finding the case for the leftmosts in all cases by recursively looking through the facts list, and then for all the leftmosts it must perform the induction steps treating them as base-cases. This is  
