# A Setoid Universe In Coq

A universe hierarchy for proof-relevant setoids, only using Coq's indexed
inductive types.

-------

Using our universe hierarchy, we get a shallow embedding of an observational
type theory that supports:
- Pi-types, Sigma-types, W-types, Integers
- Impredicative propositions
- Equality proofs in Prop that compute
- Propositional UIP (but not definitional UIP!)
- Function extensionality, proposition extensionality
- Large elimination of the accessibility predicate
- Quotients

In other words, we have the full CIC augmented with extensionality principles
and quotients. However, eta expansion for function types only holds up to a
propositional equality.

-------

Alternatively, we can put the equalities in Type, which provides us with
unique choice/function comprehension at the cost of losing impredicative
quantification.

-------

The Coq proof has been tested to compile with Coq 8.16.1