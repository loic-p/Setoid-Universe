# A Universe for Proof-relevant Setoids in Coq

A new construction for a universe of setoids, only using Coq's indexed inductive
types. The construction is agnostic regarding the nature of the setoid equality,
which can be defined in Prop, Type or SProp.

Using our universe hierarchy, we can get a shallow embedding of an observational
type theory in Coq. The precise properties that are supported by the embedded
theory depend on the sort that has been chosen for the setoid equality:

|                                          | Prop          | Type          | SProp         |
| ---------------------------------------- | ------------- | ------------- | ------------- |
| Pi-types, Sigma-types, W-types, Integers | ✅             | ✅             | ✅             |
| Universes                                | ✅             | ✅             | ✅             |
| Sort of propositions                     | Impredicative | Predicative   | Impredicative |
| Quotient types                           | ✅             | ✅             | ✅             |
| Observational equality with typecasting  | ✅             | ✅             | ✅             |
| UIP                                      | Propositional | Propositional | Definitional |
| Funext, Propext                          | ✅             | ✅             | ✅             |
| Unique choice                            | ❌             | ✅             | ❌             |
| Large elimination of accessibility       | ✅             | ✅             | ❌             |
| Eta expansion for functions              | Propositional | Propositional | Definitional |

-------

The Coq proof has been tested to compile with Coq 8.16.1
