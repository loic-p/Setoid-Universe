# A Universe for Proof-relevant Setoids in Coq

A new construction for a universe of setoids, only using Coq's indexed inductive
types. The construction is agnostic regarding the nature of the setoid equality,
which can be defined in Prop, Type or SProp.

Using our universe hierarchy, we can get a shallow embedding of an observational
type theory in Coq. The precise properties that are supported by the embedded
theory depend on the sort that has been chosen for the setoid equality:

|                                          | Prop          | Type          | SProp         | Impredicative-Set |
| ---------------------------------------- | ------------- | ------------- | ------------- | ----------------- |
| Pi-types, Sigma-types, W-types, Integers | ✅             | ✅             | ✅             | ✅                 |
| Universes                                | ✅             | ✅             | ✅             | ✅                 |
| Sort of propositions                     | Impredicative | Predicative   | Impredicative | Impredicative     |
| Quotient types                           | ✅             | ✅             | ✅             | ✅                 |
| Observational equality with typecasting  | ✅             | ✅             | ✅             | ✅                 |
| UIP                                      | Propositional | Propositional | Definitional  | Propositional     |
| Funext, Propext                          | ✅             | ✅             | ✅             | ✅                 |
| Unique choice                            | ❌             | ✅             | ❌             | ❌                 |
| Countable choice                         | ❌             | ✅             | ❌             | ❌                 |
| Dependent choice                         | ❌             | ✅             | ❌             | ❌                 |
| N -> N indexed choice                    | ❌             | Needs meta-funext  | ❌             | ❌                 |
| Large elimination of accessibility       | ✅             | ✅             | ❌             | ✅                 |
| Eta expansion for functions              | Propositional | Propositional | Definitional  | Propositional     |
| Substitutions commuting with binders     | Propositional | Propositional | Definitional  | Propositional     |
| Computation of J on reflexivity          | Propositional | Definitional  | Propositional | Definitional      |

-------

The files in `impredicative_universe` use equalities in Prop, the files in `predicative_universe` use equalities in Type.
Description of the files:
- `utils.v` : Auxiliary definitions and lemmas
- `univ0.v` : Definition of the lowest universe U0 and its induction principle
- `univ0_lemmas.v` : Reflexivity, Symmetry, Transitivity and Typecasting for the equality on U0
- `univ1.v` : Definition of the larger universe U1 and its induction principle
- `univ1_lemmas.v` : Reflexivity, Symmetry, Transitivity and Typecasting for the equality on U1
- `model.v` : Shallow embedding of the observational type theory

-------

To typecheck the development, go into one of the folders and run "make".
The Coq proof has been tested to compile with Coq 8.16.1
