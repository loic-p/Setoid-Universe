(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the definition of the large universe U1 *)

Set Universe Polymorphism.
Set Primitive Projections.
Require Import utils.
Require Import univ0 univ0_lemmas.

(* The process is similar to the definition of U0 *)

Inductive inU1@{i j k} : Type@{j} -> Type@{k} :=
| cEmb1 : forall (A : U0@{i j k}), inU1 (El0 A)
| cProp1 : inU1 Type@{i}
| cU01 : inU1 U0@{i j k}
| cPi1 : forall (A : Type@{j}) (Au : inU1 A) (Aeq : A -> A -> Type@{j})
                (P : A -> Type@{j}) (Pu : forall (a : A), inU1 (P a))
                (Peq : forall (a0 : A) (a1 : A) (p0 : P a0) (p1 : P a1), Type@{j}),
    inU1 (Sigma (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : Aeq a0 a1), Peq a0 a1 (f a0) (f a1))).

Definition inU1_eq@{i j k} {A : Type@{j}} (Au : inU1@{i j k} A) {B : Type@{j}} (Bu : inU1@{i j k} B) (a : A) (b : B) : Type@{j}.
Proof.
  revert B Bu a b. induction Au as [ A | | | A Au IHA Aeq P Pu IHP Peq ].
  - intros _ [ B | | | ].
    + exact (fun a b => eq0 A B a b).
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
  - intros _ [ | | | ].
    + exact (fun _ _ => False).
    + exact (fun P Q => P <--> Q).
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
  - intros _ [ | | | ].
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
    + exact eqU0.
    + exact (fun _ _ => False).
  - intros _ [ | | | B Bu Beq Q Qu Qeq ].
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
    + intros [ f fe ] [ g ge ].
      exact (forall a b, IHA B Bu a b -> IHP a (Q b) (Qu b) (f a) (g b)).
Defined.

Definition inU1_eqU@{i j k l} {A : Type@{j}} (Au : inU1@{i j k} A) {B : Type@{j}} (Bu : inU1@{i j k} B) : Type@{k}.
Proof.
  revert B Bu.
  (* induction Au as [ A | | A Au IHA Aeq P Pu IHP Peq ]. *)
  refine (inU1_rect@{i j k l} (fun (A0 : Type@{j}) (_ : inU1@{i j k} A0) => forall (B0 : Type@{j}) (_ : inU1@{i j k} B0), Type@{k}) (fun A => _) _ _ (fun A Au IHA Aeq P Pu IHP Peq => _) A Au).
  - intros _ [ B | | | ].
    + exact (eqU0 A B).
    + exact False.
    + exact False.
    + exact False.
  - intros _ [ | | | ].
    + exact False.
    + exact True.
    + exact False.
    + exact False.
  - intros _ [ | | | ].
    + exact False.
    + exact False.
    + exact True.
    + exact False.
  - intros _ [ | | | B Bu Beq Q Qu Qeq ].
    + exact False.
    + exact False.
    + exact False.
    + exact ((IHA B Bu) × (forall a b, inU1_eq Au Bu a b -> IHP a (Q b) (Qu b))).
Defined.

Inductive extU1@{i j k l} : forall (A : Type@{j}) (Au : inU1@{i j k} A), Type@{k} :=
| extEmb1 : forall (A : U0@{i j k}), extU1 (El0 A) (cEmb1 A)
| extProp1 : extU1 Type@{i} cProp1
| extU01 : extU1 U0@{i j k} cU01
| extPi1 : forall (A : Type@{j}) (Au : inU1 A) (Ae : extU1 A Au)
                  (P : A -> Type@{j}) (Pu : forall a, inU1 (P a))
                  (Pext : forall a0 a1, inU1_eq Au Au a0 a1 -> inU1_eqU@{i j k l} (Pu a0) (Pu a1))
                  (Pe : forall a, extU1 (P a) (Pu a)),
    extU1 (Sigma (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : inU1_eq Au Au a0 a1), inU1_eq (Pu a0) (Pu a1) (f a0) (f a1)))
      (cPi1 A Au (inU1_eq Au Au) P Pu (fun a0 a1 b0 b1 => inU1_eq (Pu a0) (Pu a1) b0 b1)).

(* Definition of the universe of large types *)

Record U1@{i j k l} : Type@{k} :=
  mkU1 {
      El1 : Type@{j} ;
      in1 : inU1@{i j k} El1 ;
      ext1 : extU1@{i j k l} El1 in1
  }.
Arguments mkU1 {_} {_}.

(* Equalities *)

Check (El1 : U1 -> Type).

Definition eq1 (A B : U1) (a : El1 A) (b : El1 B) : Type :=
  inU1_eq (in1 A) (in1 B) a b.

Definition eqU1 (A B : U1) : Type :=
  inU1_eqU (in1 A) (in1 B).

(* Constructors *)

Definition emb1 : U0 -> U1 := fun A => mkU1 (extEmb1 A).
Definition U01 : U1 := mkU1 extU01.
Definition Prop01 : U1 := mkU1 extProp1.
Definition Pi1 (A : U1) (B : El1 A -> U1) (Be : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (B a0) (B a1)) : U1 :=
  mkU1 (extPi1 (El1 A) (in1 A) (ext1 A)
              (fun a => El1 (B a)) (fun a => in1 (B a))
              Be (fun a => ext1 (B a))).

(* Induction principles *)

Definition U1_rect@{i j k l m} (X : U1@{i j k l} -> Type@{m}) :
  forall (Xemb : forall (A : U0), X (emb1 A))
         (XProp : X Prop01)
         (XU : X U01)
         (Xpi : forall (A : U1) (IHA : X A) (P : El1 A -> U1) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1)), X (Pi1 A P Pe))
         (A : U1), X A.
Proof.
  intros.
  destruct A as [A Au Ae]. induction Ae as [ A | | | A Au Ae IHA P Pu Pext Pe IHP ].
  - exact (Xemb A).
  - exact XProp.
  - exact XU.
  - exact (Xpi (mkU1 Ae) IHA (fun a => mkU1 (Pe a)) IHP Pext).
Defined.

Definition U1_rect2@{i j k l m} (X : forall (A B : U1@{i j k l}), eqU1 A B -> Type@{m}) :
  forall (Xemb : forall (A B : U0@{i j k}) (eAB : eqU0 A B), X (emb1 A) (emb1 B) eAB)
         (XProp : X Prop01 Prop01 I)
         (XU : X U01 U01 I)
         (Xpi : forall (A B : U1@{i j k l}) (eAB : eqU1 A B) (IHA : X A B eAB) (P : El1 A -> U1@{i j k l}) (Q : El1 B -> U1@{i j k l})
                       (ePQ : forall a b, eq1 A B a b -> eqU1 (P a) (Q b))
                       (IHP : forall a b (eab : eq1 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1))
                       (Qe : forall b0 b1 : El1 B, eq1 B B b0 b1 -> eqU1 (Q b0) (Q b1)),
             X (Pi1 A P Pe) (Pi1 B Q Qe) (mkAndEx eAB ePQ))
         (A B : U1@{i j k l}) (e : eqU1 A B), X A B e.
Proof.
  intros Xemb XProp XU Xpi A.
  pattern A ; eapply U1_rect@{i j k l m} ; clear A.
  - intros A B. pattern B ; eapply U1_rect@{i j k l m} ; now intros [].
  - intro B. pattern B ; eapply U1_rect@{i j k l m} ; now intros [].
  - intro B. pattern B ; eapply U1_rect@{i j k l m} ; now intros [].
  - intros A IHA P IHP Pe B. pattern B ; eapply U1_rect@{i j k l m} ; try (now intros []).
    clear B. intros B _ Q _ Qe [eAB ePQ]. eapply Xpi.
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
Defined.
