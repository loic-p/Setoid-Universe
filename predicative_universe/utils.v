(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the basic datatypes and lemmas that we will use in our
   development *)

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.

(* Basic datatypes *)

Inductive nat@{i} : Type@{i} :=
| zero : nat
| suc : nat -> nat.

Inductive empty@{i} : Type@{i} :=.

Inductive unit@{i} : Type@{i} :=
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

Record and_ex@{i} (A B : Type@{i}) : Type@{i} :=
  mkAndEx {
    andleft : A;
    andright : B;
  }.
Arguments mkAndEx {_} {_}.
Arguments andleft {_} {_}.
Arguments andright {_} {_}.
Notation "A × B" := (and_ex A B) (at level 80, right associativity).

Definition bi_impl@{i} (A B : Type@{i}) : Type@{i} := (A -> B) × (B -> A).
Notation "A <--> B" := (bi_impl A B) (at level 90).

Lemma biimpl_refl (A : Type) : A <--> A.
Proof.
  easy.
Defined.

Lemma biimpl_sym [A B : Type] : A <--> B -> B <--> A.
Proof.
  now intros [ H1 H2 ].
Defined.

Lemma biimpl_trans [A B C : Type] : A <--> B -> B <--> C -> A <--> C.
Proof.
  intros [ H1 H2 ] [ H3 H4 ]. split ; tauto.
Defined.

(* Reflective, symmetric, transitive closure of a relation R on a setoid whose equality is eA *)

Inductive closure@{i} {A : Type@{i}} (eA : A -> A -> Type@{i}) (R : A -> A -> Type@{i}) : A -> A -> Type@{i} :=
| clo_emb : forall a b, R a b -> closure eA R a b
| clo_refl : forall a b, eA a b -> closure eA R a b
| clo_sym : forall a b, closure eA R a b -> closure eA R b a
| clo_trans : forall a b c, closure eA R a b -> closure eA R b c -> closure eA R a c.
Arguments clo_emb {_} {_} {_}.
Arguments clo_refl {_} {_} {_}.
Arguments clo_sym {_} {_} {_}.
Arguments clo_trans {_} {_} {_}.

(* Setoid equality on the natural numbers *)

Inductive nateq@{i} : nat@{i} -> nat@{i} -> Type@{i} :=
| eqzero : nateq zero zero
| eqsuc : forall (n m : nat), nateq n m -> nateq (suc n) (suc m).

Theorem nateq_refl : forall (n : nat), nateq n n.
Proof.
  intros. induction n ; now constructor.
Defined.

Theorem nateq_sym : forall {n m}, nateq n m -> nateq m n.
Proof.
  intros. induction X ; now constructor.
Defined.

Theorem nateq_trans : forall {n m l}, nateq n m -> nateq m l -> nateq n l.
Proof.
  intros n m l H. revert l. induction H.
  - easy.
  - intros l Hl. inversion Hl as [|? l0]. constructor. now apply IHnateq.
Defined.

Theorem nateq_eq : forall {n m}, nateq n m -> n = m.
Proof.
  intros. induction X.
  - easy.
  - eapply f_equal. exact IHX.
Defined.

Theorem suc_inj : forall {n m}, suc n = suc m -> n = m.
Proof.
  intros. inversion H. easy.
Defined.

Theorem eq_nateq : forall {n m}, n = m -> nateq n m.
Proof.
  intro n. induction n.
  - intro m. induction m.
    + intros. econstructor.
    + easy.
  - intro m. destruct m.
    + easy.
    + intro H. apply eqsuc. apply IHn. apply suc_inj. exact H.
Defined.

Theorem nateq_iso : forall {n m} (e : nateq n m), e = eq_nateq (nateq_eq e).
Proof.
  intros n m e. induction e.
  - reflexivity.
  - change (eqsuc n m e = eq_nateq (f_equal suc (nateq_eq e))).
    change (eqsuc n m e = eqsuc n m (eq_nateq (suc_inj (f_equal suc (nateq_eq e))))).
    apply (f_equal (eqsuc n m)). refine (eq_trans IHe _).
    apply (f_equal eq_nateq).
    assert (forall n m (e : n = m), e = suc_inj (f_equal suc e)).
    { clear n m e IHe. intros n m e. destruct e. reflexivity. }
    eapply H.
Defined.

Definition nateq2 : nat -> nat -> Type.
Proof.
  intro n. induction n.
  - intro m. destruct m.
    + exact unit.
    + exact empty.
  - intro m. destruct m.
    + exact empty.
    + exact (IHn m).
Defined.

Definition nateq2_refl : forall (n : nat), nateq2 n n.
Proof.
  intro n. induction n.
  - exact tt.
  - exact IHn.
Defined.

Definition eq_nateq2 : forall {n m : nat}, n = m -> nateq2 n m.
Proof.
  intros n m e. destruct e. apply nateq2_refl.
Defined.

Definition nateq2_eq : forall {n m : nat}, nateq2 n m -> n = m.
Proof.
  intro n.
  induction n.
  - intro m ; destruct m.
    + intros. reflexivity.
    + intros. destruct X.
  - intro m ; destruct m.
    + intros. destruct X.
    + intros. apply (IHn m) in X.
      apply (f_equal suc). exact X.
Defined.

Definition nateq2_iso : forall (n m : nat) (e : n = m), e = nateq2_eq (eq_nateq2 e).
Proof.
  intros n m e. destruct e.
  simpl. induction n.
  - reflexivity.
  - change (eq_refl = f_equal suc (nateq2_eq (nateq2_refl n))).
    rewrite <- IHn. reflexivity.
Defined.

Definition nateq2_hprop : forall {n m : nat} (e1 e2 : nateq2 n m), e1 = e2.
Proof.
  intro n. induction n.
  - destruct m.
    + destruct e1 ; destruct e2 ; easy.
    + easy.
  - destruct m.
    + easy.
    + apply IHn.
Defined.

Definition eq_hprop : forall {n m : nat} (e1 e2 : n = m), e1 = e2.
Proof.
  intros n m e1 e2.
  rewrite (nateq2_iso n m e1).
  rewrite (nateq2_hprop (eq_nateq2 e1) (eq_nateq2 e2)).
  rewrite <- (nateq2_iso n m e2).
  reflexivity.
Defined.

Definition nateq_hprop : forall {n m : nat} (e1 e2 : nateq n m), e1 = e2.
Proof.
  intros n m e1 e2.
  rewrite (nateq_iso e1).
  rewrite (eq_hprop (nateq_eq e1) (nateq_eq e2)).
  rewrite <- (nateq_iso e2).
  reflexivity.
Defined.

(* Setoid equality on W types *)
(* The equality is parameterised by a setoid equality on A and B *)

Inductive Weq@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> Type@{i})
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Type@{i})
  : W A0 B0 -> W A1 B1 -> Type@{i} :=
| eqsup : forall (a0 : A0) (a1 : A1) (ae : Aeq a0 a1)
                 (f0 : forall (b0 : B0 a0), W A0 B0) (f1 : forall (b1 : B1 a1), W A1 B1)
                 (fe : forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1))
  , Weq Aeq Beq (sup a0 f0) (sup a1 f1).

Arguments eqsup {_} {_} {_} {_} {_} {_}.

Definition Weq_step@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> Type@{i})
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Type@{i})
  (w0 : W A0 B0) (w1 : W A1 B1) : Type@{i} :=
  match w0 with
  | sup a0 f0 => match w1 with
                 | sup a1 f1 => Aeq a0 a1 × forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1)
                 end
  end.

Definition Weq_step_lemma@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> Type@{i})
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Type@{i})
  (w0 : W A0 B0) (w1 : W A1 B1) (we : Weq Aeq Beq w0 w1) : Weq_step Aeq Beq w0 w1.
Proof.
  destruct we as [ a0 a1 ae f0 f1 fe ].
  now split.
Defined.

Definition Weq_inversion {A0 A1 : Type} {Aeq : A0 -> A1 -> Type}
  {B0 : A0 -> Type} {B1 : A1 -> Type} {Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Type}
  {a0 : A0} {a1 : A1} {f0 : forall (b0 : B0 a0), W A0 B0} {f1 : forall (b1 : B1 a1), W A1 B1}
  : Weq Aeq Beq (sup a0 f0) (sup a1 f1) -> Aeq a0 a1 × forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1).
Proof.
  intro e. apply (Weq_step_lemma Aeq Beq _ _) in e. exact e.
Defined.


(* Inductive predicate that carves out the W-types that contain setoid functions *)

Inductive Wext@{i} (A : Type@{i}) (Aeq : A -> A -> Type@{i})
  (B : A -> Type@{i}) (Beq : forall a0 a1 : A, B a0 -> B a1 -> Type@{i}) : W A B -> Type@{i} :=
| extsup : forall (a : A)
                  (f : forall (b : B a), W A B)
                  (fe : forall (b : B a), Wext A Aeq B Beq (f b))
                  (fext : forall (b0 b1 : B a) (be : Beq a a b0 b1), Weq Aeq Beq (f b0) (f b1))
  , Wext A Aeq B Beq (sup a f).
Arguments extsup {_} {_} {_} {_}.
