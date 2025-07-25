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
| cEmb1 : forall (A : U0@{i j}), inU1 (El0 A)
| cU01 : inU1 U0@{i j}
| cSigma : forall (A : Type@{j}) (Au : inU1 A)
                  (P : A -> Type@{j}) (Pu : forall (a : A), inU1 (P a)),
    inU1 (Sigma A P)
| cPi1 : forall (A : Type@{j}) (Au : inU1 A) (Aeq : A -> A -> SProp)
                (P : A -> Type@{j}) (Pu : forall (a : A), inU1 (P a))
                (Peq : forall (a0 : A) (a1 : A) (p0 : P a0) (p1 : P a1), SProp),
    inU1 (Sigmas (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : Aeq a0 a1), Peq a0 a1 (f a0) (f a1))).

Definition inU1_eq@{i j k} {A : Type@{j}} (Au : inU1@{i j k} A) {B : Type@{j}} (Bu : inU1@{i j k} B) (a : A) (b : B) : SProp.
Proof.
  revert B Bu a b. induction Au as [ A | | A Au IHA P Pu IHP | A Au IHA Aeq P Pu IHP Peq ].
  - intros _ [ B | | | ].
    2,3,4: exact (fun _ _ => sFalse).
    exact (fun a b => eq0 A B a b).
  - intros _ [ | | | ].
    1,3,4: exact (fun _ _ => sFalse).
    exact eqU0.
  - intros _ [ | | B Bu Q Qu | ].
    1,2,4: exact (fun _ _ => sFalse).
    intros [ a p ] [ b q ].
    exact (and_ex (IHA B Bu a b) (IHP a (Q b) (Qu b) p q)).
  - intros _ [ | | | B Bu Beq Q Qu Qeq ].
    1,2,3: exact (fun _ _ => sFalse).
    intros [ f fe ] [ g ge ].
    exact (forall a b, IHA B Bu a b -> IHP a (Q b) (Qu b) (f a) (g b)).
Defined.

Definition inU1_eqU@{i j k} {A : Type@{j}} (Au : inU1@{i j k} A) {B : Type@{j}} (Bu : inU1@{i j k} B) : SProp.
Proof.
  revert B Bu. induction Au as [ A | | A Au IHA P Pu IHP | A Au IHA Aeq P Pu IHP Peq ].
  - intros _ [ B | | | ].
    2,3,4: exact sFalse.
    exact (eqU0 A B).
  - intros _ [ | | | ].
    1,3,4: exact sFalse.
    exact sTrue.
  - intros _ [ | | B Bu Q Qu | ].
    1,2,4: exact sFalse.
    exact (sand (IHA B Bu) (forall a b, inU1_eq Au Bu a b -> IHP a (Q b) (Qu b))).
  - intros _ [ | | | B Bu Beq Q Qu Qeq ].
    1,2,3: exact sFalse.
    exact (sand (IHA B Bu) (forall a b, inU1_eq Au Bu a b -> IHP a (Q b) (Qu b))).
Defined.

Inductive extU1@{i j k} : forall (A : Type@{j}) (Au : inU1@{i j k} A), Type@{k} :=
| extEmb1 : forall (A : U0), extU1 (El0 A) (cEmb1 A)
| extU01 : extU1 U0 cU01
| extSigma1 : forall (A : Type@{j}) (Au : inU1 A) (Ae : extU1 A Au)
                    (P : A -> Type@{j}) (Pu : forall a, inU1 (P a))
                    (Pext : forall a0 a1, inU1_eq Au Au a0 a1 -> inU1_eqU (Pu a0) (Pu a1))
                    (Pe : forall a, extU1 (P a) (Pu a)),
    extU1 (Sigma A P) (cSigma A Au P Pu)
| extPi1 : forall (A : Type@{j}) (Au : inU1 A) (Ae : extU1 A Au)
                  (P : A -> Type@{j}) (Pu : forall a, inU1 (P a))
                  (Pext : forall a0 a1, inU1_eq Au Au a0 a1 -> inU1_eqU (Pu a0) (Pu a1))
                  (Pe : forall a, extU1 (P a) (Pu a)),
    extU1 (Sigmas (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : inU1_eq Au Au a0 a1), inU1_eq (Pu a0) (Pu a1) (f a0) (f a1)))
      (cPi1 A Au (inU1_eq Au Au) P Pu (fun a0 a1 b0 b1 => inU1_eq (Pu a0) (Pu a1) b0 b1)).

(* Definition of the universe of large types *)

Record U1@{i j k} : Type@{k} :=
  mkU1 {
      El1 : Type@{j} ;
      in1 : inU1@{i j k} El1 ;
      ext1 : extU1@{i j k} El1 in1
  }.
Arguments mkU1 {_} {_}.

(* Equalities *)

Check (El1 : U1 -> Type).

Definition eq1 (A B : U1) (a : El1 A) (b : El1 B) : SProp :=
  inU1_eq (in1 A) (in1 B) a b.

Definition eqU1 (A B : U1) : SProp :=
  inU1_eqU (in1 A) (in1 B).

(* Constructors *)

Definition emb1 : U0 -> U1 := fun A => mkU1 (extEmb1 A).
Definition U01 : U1 := mkU1 extU01.
Definition Sigma1 (A : U1) (B : El1 A -> U1) (Be : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (B a0) (B a1)) : U1 :=
  mkU1 (extSigma1 (El1 A) (in1 A) (ext1 A)
              (fun a => El1 (B a)) (fun a => in1 (B a))
              Be (fun a => ext1 (B a))).
Definition Pi1 (A : U1) (B : El1 A -> U1) (Be : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (B a0) (B a1)) : U1 :=
  mkU1 (extPi1 (El1 A) (in1 A) (ext1 A)
              (fun a => El1 (B a)) (fun a => in1 (B a))
              Be (fun a => ext1 (B a))).

(* Induction principles *)

Definition U1_rect@{i j k l} (X : U1@{i j k} -> Type@{l}) :
  forall (Xemb : forall (A : U0), X (emb1 A))
         (XU : X U01)
         (Xsigma : forall (A : U1) (IHA : X A) (P : El1 A -> U1) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1)), X (Sigma1 A P Pe))
         (Xpi : forall (A : U1) (IHA : X A) (P : El1 A -> U1) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1)), X (Pi1 A P Pe))
         (A : U1), X A.
Proof.
  intros.
  destruct A as [A Au Ae]. induction Ae as [ A | | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA P Pu Pext Pe IHP ].
  - exact (Xemb A).
  - exact XU.
  - exact (Xsigma (mkU1 Ae) IHA (fun a => mkU1 (Pe a)) IHP Pext).
  - exact (Xpi (mkU1 Ae) IHA (fun a => mkU1 (Pe a)) IHP Pext).
Defined.

Definition U1_ind@{i j k} (X : U1@{i j k} -> SProp) :
  forall (Xemb : forall (A : U0), X (emb1 A))
         (XU : X U01)
         (Xsigma : forall (A : U1) (IHA : X A) (P : El1 A -> U1) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1)), X (Sigma1 A P Pe))
         (Xpi : forall (A : U1) (IHA : X A) (P : El1 A -> U1) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1)), X (Pi1 A P Pe))
         (A : U1), X A.
Proof.
  intros.
  destruct A as [A Au Ae]. induction Ae as [ A | | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA P Pu Pext Pe IHP ].
  - exact (Xemb A).
  - exact XU.
  - exact (Xsigma (mkU1 Ae) IHA (fun a => mkU1 (Pe a)) IHP Pext).
  - exact (Xpi (mkU1 Ae) IHA (fun a => mkU1 (Pe a)) IHP Pext).
Defined.

Definition U1_rect2@{i j k l} (X : forall (A B : U1@{i j k}), eqU1 A B -> Type@{l}) :
  forall (Xemb : forall (A B : U0@{i j}) (eAB : eqU0 A B), X (emb1 A) (emb1 B) eAB)
         (XU : X U01 U01 stt)
         (Xsigma : forall (A B : U1@{i j k}) (eAB : eqU1 A B) (IHA : X A B eAB) (P : El1 A -> U1@{i j k}) (Q : El1 B -> U1@{i j k})
                       (ePQ : forall a b, eq1 A B a b -> eqU1 (P a) (Q b))
                       (IHP : forall a b (eab : eq1 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1))
                       (Qe : forall b0 b1 : El1 B, eq1 B B b0 b1 -> eqU1 (Q b0) (Q b1)),
             X (Sigma1 A P Pe) (Sigma1 B Q Qe) (sand_intro eAB ePQ))
         (Xpi : forall (A B : U1@{i j k}) (eAB : eqU1 A B) (IHA : X A B eAB) (P : El1 A -> U1@{i j k}) (Q : El1 B -> U1@{i j k})
                       (ePQ : forall a b, eq1 A B a b -> eqU1 (P a) (Q b))
                       (IHP : forall a b (eab : eq1 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1))
                       (Qe : forall b0 b1 : El1 B, eq1 B B b0 b1 -> eqU1 (Q b0) (Q b1)),
             X (Pi1 A P Pe) (Pi1 B Q Qe) (sand_intro eAB ePQ))
         (A B : U1@{i j k}) (e : eqU1 A B), X A B e.
Proof.
  intros Xemb XU Xsigma Xpi A.
  pattern A ; eapply U1_rect@{i j k l} ; clear A.
  - intros A B. pattern B ; eapply U1_rect@{i j k l} ; now intros [].
  - intro B. pattern B ; eapply U1_rect@{i j k l} ; try (now intros []).
    intros. exact XU.
  - intros A IHA P IHP Pe B. pattern B ; eapply U1_rect@{i j k l} ; try (now intros []).
    clear B. intros B _ Q _ Qe e. pose proof (sand_fst e) as eAB. pose proof (sand_snd e) as ePQ.
    refine (Xsigma A B eAB _ P Q ePQ _ Pe Qe).
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
  - intros A IHA P IHP Pe B. pattern B ; eapply U1_rect@{i j k l} ; try (now intros []).
    clear B. intros B _ Q _ Qe e. pose proof (sand_fst e) as eAB. pose proof (sand_snd e) as ePQ.
    refine (Xpi A B eAB _ P Q ePQ _ Pe Qe).
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
Defined.

Definition U1_ind2@{i j k} (X : forall (A B : U1@{i j k}), eqU1 A B -> SProp) :
  forall (Xemb : forall (A B : U0@{i j}) (eAB : eqU0 A B), X (emb1 A) (emb1 B) eAB)
         (XU : X U01 U01 stt)
         (Xsigma : forall (A B : U1@{i j k}) (eAB : eqU1 A B) (IHA : X A B eAB) (P : El1 A -> U1@{i j k}) (Q : El1 B -> U1@{i j k})
                       (ePQ : forall a b, eq1 A B a b -> eqU1 (P a) (Q b))
                       (IHP : forall a b (eab : eq1 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1))
                       (Qe : forall b0 b1 : El1 B, eq1 B B b0 b1 -> eqU1 (Q b0) (Q b1)),
             X (Sigma1 A P Pe) (Sigma1 B Q Qe) (sand_intro eAB ePQ))
         (Xpi : forall (A B : U1@{i j k}) (eAB : eqU1 A B) (IHA : X A B eAB) (P : El1 A -> U1@{i j k}) (Q : El1 B -> U1@{i j k})
                       (ePQ : forall a b, eq1 A B a b -> eqU1 (P a) (Q b))
                       (IHP : forall a b (eab : eq1 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1))
                       (Qe : forall b0 b1 : El1 B, eq1 B B b0 b1 -> eqU1 (Q b0) (Q b1)),
             X (Pi1 A P Pe) (Pi1 B Q Qe) (sand_intro eAB ePQ))
         (A B : U1@{i j k}) (e : eqU1 A B), X A B e.
Proof.
  intros Xemb XU Xsigma Xpi A.
  pattern A ; eapply U1_ind@{i j k} ; clear A.
  - intros A B. pattern B ; eapply U1_ind@{i j k} ; now intros [].
  - intro B. pattern B ; eapply U1_ind@{i j k} ; try (now intros []).
  - intros A IHA P IHP Pe B. pattern B ; eapply U1_ind@{i j k} ; try (now intros []).
    clear B. intros B _ Q _ Qe e. pose proof (sand_fst e) as eAB. pose proof (sand_snd e) as ePQ.
    refine (Xsigma A B eAB _ P Q ePQ _ Pe Qe).
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
  - intros A IHA P IHP Pe B. pattern B ; eapply U1_ind@{i j k} ; try (now intros []).
    clear B. intros B _ Q _ Qe e. pose proof (sand_fst e) as eAB. pose proof (sand_snd e) as ePQ.
    refine (Xpi A B eAB _ P Q ePQ _ Pe Qe).
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
Defined.
