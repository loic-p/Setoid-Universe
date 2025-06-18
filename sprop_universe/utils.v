(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the basic datatypes and lemmas that we will use in our
   development *)

Set Universe Polymorphism.
Set Primitive Projections.

(* Basic datatypes *)

Inductive nat : Type@{Set} :=
| zero : nat
| suc : nat -> nat.

Inductive empty : Type@{Set} :=.

Inductive unit : Type@{Set} :=
| tt : unit.

Inductive W@{i} (A : Type@{i}) (B : A -> Type@{i}) : Type@{i} :=
| sup : forall (a : A) (f : B a -> W A B), W A B.
Arguments sup {_} {_}.

(* "Strong" Sigma-types *)

Record Sigma@{i j} (A : Type@{i}) (B : A -> Type@{j}) : Type@{max(i,j)} :=
  mkPair {
    fst : A;
    snd : B fst;
  }.
Arguments mkPair {_} {_}.
Arguments fst {_} {_}.
Arguments snd {_} {_}.


(* "Strong" logical conjunction *)

Record and_ex (A B : SProp) : SProp :=
  mkAndEx {
    andleft : A;
    andright : B;
  }.
Arguments mkAndEx {_} {_}.
Arguments andleft {_} {_}.
Arguments andright {_} {_}.

(* Accessibility predicate, and a beefed up induction principle *)

(* Reflective, symmetric, transitive closure of a relation R on a setoid whose equality is eA *)
Inductive closure {A : Type} (eA : A -> A -> SProp) (R : A -> A -> SProp) : A -> A -> SProp :=
| clo_emb : forall a b, R a b -> closure eA R a b
| clo_refl : forall a b, eA a b -> closure eA R a b
| clo_sym : forall a b, closure eA R a b -> closure eA R b a
| clo_trans : forall a b c, closure eA R a b -> closure eA R b c -> closure eA R a c.
Arguments clo_emb {_} {_} {_}.
Arguments clo_refl {_} {_} {_}.
Arguments clo_sym {_} {_} {_}.
Arguments clo_trans {_} {_} {_}.

(* Forded identity type *)

Inductive fordedId@{i} (A : Type@{i}) (Ae : A -> A -> SProp) (a : A) : A -> Type@{i} :=
| frefl : fordedId A Ae a a
| forded : forall (b : A), Ae a b -> fordedId A Ae a b.
Arguments frefl {_} {_} {_}.
Arguments forded {_} {_} {_} {_}.

Definition obseq_of_fordedId (A : Type) (Ae : A -> A -> SProp) (refl : forall a, Ae a a) (a b : A) : fordedId A Ae a b -> Ae a b.
Proof.
  intro p. destruct p as [ | b p ].
  - apply refl.
  - exact p.
Defined.

(* Setoid equality on the natural numbers *)

Inductive nateq : nat -> nat -> SProp :=
| eqzero : nateq zero zero
| eqsuc : forall (n m : nat), nateq n m -> nateq (suc n) (suc m).

Theorem nateq_refl : forall (n : nat), nateq n n.
Proof.
  intros. induction n ; now constructor.
Defined.

Theorem nateq_sym : forall {n m}, nateq n m -> nateq m n.
Proof.
  intros. induction H ; now constructor.
Defined.

Theorem nateq_trans : forall {n m l}, nateq n m -> nateq m l -> nateq n l.
Proof.
  intros n m l H. revert l. induction H.
  - easy.
  - intros l Hl. inversion Hl as [|? l0]. constructor. now apply IHnateq.
Defined.

Inductive sand (A B : SProp) : SProp :=
| sand_intro : A -> B -> sand A B.
Arguments sand_intro {_} {_}.

Definition sand_fst {A B : SProp} : sand A B -> A.
intros [f s]. exact f. Defined.

Definition sand_snd {A B : SProp} : sand A B -> B.
intros [f s]. exact s. Defined.

Inductive to_set (A : SProp) : Set :=
| to_set_intro : forall (a : A) , to_set A.

Definition to_set_esc (A : SProp) : to_set A -> A.
Proof.
  intro a. destruct a. exact a.
Defined.

Inductive sFalse : SProp :=.
Inductive sTrue : SProp := stt : sTrue.

Record Sigmas@{i} (A : Type@{i}) (B : A -> SProp) : Type@{i} :=
  mkPairs {
    fsts : A;
    snds : B fsts;
  }.
Arguments mkPairs {_} {_}.
Arguments fsts {_} {_}.
Arguments snds {_} {_}.

Inductive sexists@{i} (A : Type@{i}) (B : A -> SProp) : SProp :=
| sexists_intro : forall (a : A) (b : B a), sexists A B.


(* Setoid equality on W types *)
(* The equality is parameterised by a setoid equality on A and B *)

Inductive Weq@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> SProp)
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> SProp)
  : W A0 B0 -> W A1 B1 -> SProp :=
| eqsup : forall (a0 : A0) (a1 : A1) (ae : Aeq a0 a1)
                 (f0 : forall (b0 : B0 a0), W A0 B0) (f1 : forall (b1 : B1 a1), W A1 B1)
                 (fe : forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1))
  , Weq Aeq Beq (sup a0 f0) (sup a1 f1).

Arguments eqsup {_} {_} {_} {_} {_} {_}.

Definition Weq_step@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> SProp)
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> SProp)
  (w0 : W A0 B0) (w1 : W A1 B1) : SProp :=
  match w0 with
  | sup a0 f0 => match w1 with
                 | sup a1 f1 => sand (Aeq a0 a1) (forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1))
                 end
  end.

Definition Weq_step_lemma@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> SProp)
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> SProp)
  (w0 : W A0 B0) (w1 : W A1 B1) (we : Weq Aeq Beq w0 w1) : Weq_step Aeq Beq w0 w1.
Proof.
  destruct we as [ a0 a1 ae f0 f1 fe ].
  now split.
Defined.

Definition Weq_inversion {A0 A1 : Type} {Aeq : A0 -> A1 -> SProp}
  {B0 : A0 -> Type} {B1 : A1 -> Type} {Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> SProp}
  {a0 : A0} {a1 : A1} {f0 : forall (b0 : B0 a0), W A0 B0} {f1 : forall (b1 : B1 a1), W A1 B1}
  : Weq Aeq Beq (sup a0 f0) (sup a1 f1) -> sand (Aeq a0 a1) (forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1)).
Proof.
  intro e. apply (Weq_step_lemma Aeq Beq _ _) in e. exact e.
Defined.


(* Inductive predicate that carves out the W-types that contain setoid functions *)

Inductive Wext@{i} (A : Type@{i}) (Aeq : A -> A -> SProp)
  (B : A -> Type@{i}) (Beq : forall a0 a1 : A, B a0 -> B a1 -> SProp) : W A B -> Type@{i} :=
| extsup : forall (a : A)
                  (f : forall (b : B a), W A B)
                  (fe : forall (b : B a), Wext A Aeq B Beq (f b))
                  (fext : forall (b0 b1 : B a) (be : Beq a a b0 b1), Weq Aeq Beq (f b0) (f b1))
  , Wext A Aeq B Beq (sup a f).
Arguments extsup {_} {_} {_} {_}.
