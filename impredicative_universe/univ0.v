(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the definition of the lower universe U0, with its induction principle. *)

Set Universe Polymorphism.
Set Primitive Projections.
Require Import utils.

(* The ideal definition of U0 is inductive-recursive, but IR is not supported by coq.
   So instead, we will simulate IR with ordinary inductive families:

 - First, we define the indexed datatype inU0 that encodes the graph of the El0 function.
   Since elements of Pi-types and W-types need to be extensional, but we do not have access
   to the equalities yet (no induction-recursion!), we parameterize them with some arbitrary
   notion of equality.

 - Second, we define the two equalities on inU0

 - Third, we define the datatype extU0 indexed over inU0, which ensures that the arbitrary
   equality contained in Pi-types and W-types matches the actual equality that we defined in
   step 2

 - Finally, we define an inhabitant of U0 as a small type A, a proof A' that it is inU0, and
   a proof A'' that the pair (A, A') is in extU0.
 *)

Inductive inU0@{i j} : Type@{i} -> Type@{j} :=
| cEmb0 : forall (P : Prop), inU0 P
| cN : inU0 nat
| cProp : inU0 Prop
| cSigma : forall (A : Type@{i}) (Au : inU0 A)
                  (P : A -> Type@{i}) (Pu : forall (a : A), inU0 (P a)),
    inU0 (Sigma A P)
| cPi : forall (A : Type@{i}) (Au : inU0 A) (Aeq : A -> A -> Prop)
               (P : A -> Type@{i}) (Pu : forall (a : A), inU0 (P a))
               (Peq : forall (a0 : A) (a1 : A) (p0 : P a0) (p1 : P a1), Prop),
    inU0 (Sigma (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : Aeq a0 a1), Peq a0 a1 (f a0) (f a1)))
| cW : forall (A : Type@{i}) (Au : inU0 A) (Aeq : A -> A -> Prop)
               (P : A -> Type@{i}) (Pu : forall (a : A), inU0 (P a))
               (Peq : forall (a0 : A) (a1 : A) (p0 : P a0) (p1 : P a1), Prop),
    inU0 (Sigma (W A P) (Wext A Aeq P Peq))
| cQuo : forall (A : Type@{i}) (Au : inU0 A) (Aeq : A -> A -> Prop)
                (R : A -> A -> Prop),
    inU0 A.

Definition inU0_eq@{i j} {A : Type@{i}} (Au : inU0@{i j} A) {B : Type@{i}} (Bu : inU0@{i j} B) (a : A) (b : B) : Prop.
Proof.
  revert B Bu a b. induction Au as [ P | | | A Au IHA P Pu IHP | A Au IHA Aeq P Pu IHP Peq | A Au IHA Aeq P Pu IHP Peq | A Au IHA Aeq R ].
  - intros _ [ Q | | | | | | ].
    2,3,4,5,6,7: exact (fun _ _ => False).
    exact (fun _ _ => True).
  - intros _ [ | | | | | | ].
    1,3,4,5,6,7: exact (fun _ _ => False).
    exact nateq.
  - intros _ [ | | | | | | ].
    1,2,4,5,6,7: exact (fun _ _ => False).
    exact (fun P Q => P <-> Q).
  - intros _ [ | | | B Bu Q Qu | | | ].
    1,2,3,5,6,7: exact (fun _ _ => False).
    intros [ a p ] [ b q ].
    exact (and_ex (IHA B Bu a b) (IHP a (Q b) (Qu b) p q)).
  - intros _ [ | | | | B Bu Beq Q Qu Qeq | | ].
    1,2,3,4,6,7: exact (fun _ _ => False).
    intros [ f fe ] [ g ge ].
    exact (forall a b, IHA B Bu a b -> IHP a (Q b) (Qu b) (f a) (g b)).
  - intros _ [ | | | | | B Bu Beq Q Qu Qeq | ].
    1,2,3,4,5,7: exact (fun _ _ => False).
    intros [ f fe ] [ g ge ].
    exact (Weq (fun a b => IHA B Bu a b) (fun a b p q => IHP a (Q b) (Qu b) p q) f g).
  - intros _ [ | | | | | | B Bu Beq S ].
    1,2,3,4,5,6: exact (fun _ _ => False).
    exact (fun a b => exists (a1 : A) (b1 : B), closure Aeq R a a1 /\ IHA B Bu a1 b1 /\ closure Beq S b1 b).
Defined.

Definition inU0_eqU@{i j} {A : Type@{i}} (Au : inU0@{i j} A) {B : Type@{i}} (Bu : inU0@{i j} B) : Prop.
Proof.
  revert B Bu. induction Au as [ P | | | A Au IHA P Pu IHP | A Au IHA Aeq P Pu IHP Peq | A Au IHA Aeq P Pu IHP Peq | A Au IHA Aeq R ].
  - intros _ [ Q | | | | | | ].
    2,3,4,5,6,7: exact False.
    exact (P <-> Q).
  - intros _ [ | | | | | | ].
    1,3,4,5,6,7: exact False.
    exact True.
  - intros _ [ | | | | | | ].
    1,2,4,5,6,7: exact False.
    exact True.
  - intros _ [ | | | B Bu Q Qu | | | ].
    1,2,3,5,6,7: exact False.
    exact ((IHA B Bu) /\ (forall a b, inU0_eq Au Bu a b -> IHP a (Q b) (Qu b))).
  - intros _ [ | | | | B Bu Beq Q Qu Qeq | | ].
    1,2,3,4,6,7: exact False.
    exact ((IHA B Bu) /\ (forall a b, inU0_eq Au Bu a b -> IHP a (Q b) (Qu b))).
  - intros _ [ | | | | | B Bu Beq Q Qu Qeq | ].
    1,2,3,4,5,7: exact False.
    exact ((IHA B Bu) /\ (forall a b, inU0_eq Au Bu a b -> IHP a (Q b) (Qu b))).
  - intros _ [ | | | | | | B Bu Beq S ].
    1,2,3,4,5,6: exact False.
    exact (IHA B Bu /\ (forall a0 b0 (e0 : inU0_eq Au Bu a0 b0) a1 b1 (e1 : inU0_eq Au Bu a1 b1), R a0 a1 <-> S b0 b1)).
Defined.

Inductive extU0@{i j} : forall (A : Type@{i}) (Au : inU0@{i j} A), Type@{j} :=
| extEmb0 : forall (P : Prop), extU0 P (cEmb0 P)
| extN : extU0 nat cN
| extProp : extU0 Prop cProp
| extSigma : forall (A : Type@{i}) (Au : inU0 A) (Ae : extU0 A Au)
                    (P : A -> Type@{i}) (Pu : forall a, inU0 (P a))
                    (Pext : forall a0 a1, inU0_eq Au Au a0 a1 -> inU0_eqU (Pu a0) (Pu a1))
                    (Pe : forall a, extU0 (P a) (Pu a)),
    extU0 (Sigma A P)
      (cSigma A Au P Pu)
| extPi : forall (A : Type@{i}) (Au : inU0 A) (Ae : extU0 A Au)
                 (P : A -> Type@{i}) (Pu : forall a, inU0 (P a))
                 (Pext : forall a0 a1, inU0_eq Au Au a0 a1 -> inU0_eqU (Pu a0) (Pu a1))
                 (Pe : forall a, extU0 (P a) (Pu a)),
    extU0 (Sigma (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : inU0_eq Au Au a0 a1), inU0_eq (Pu a0) (Pu a1) (f a0) (f a1)))
      (cPi A Au (inU0_eq Au Au) P Pu (fun a0 a1 b0 b1 => inU0_eq (Pu a0) (Pu a1) b0 b1))
| extW : forall (A : Type@{i}) (Au : inU0 A) (Ae : extU0 A Au)
                (P : A -> Type@{i}) (Pu : forall a, inU0 (P a))
                (Pext : forall a0 a1, inU0_eq Au Au a0 a1 -> inU0_eqU (Pu a0) (Pu a1))
                (Pe : forall a, extU0 (P a) (Pu a)),
    extU0 (Sigma (W A P) (Wext A (inU0_eq Au Au) P (fun a0 a1 b0 b1 => inU0_eq (Pu a0) (Pu a1) b0 b1)))
      (cW A Au (inU0_eq Au Au) P Pu (fun a0 a1 b0 b1 => inU0_eq (Pu a0) (Pu a1) b0 b1))
| extQuo : forall (A : Type@{i}) (Au : inU0 A) (Ae : extU0 A Au) (R : A -> A -> Prop)
                  (Rext : forall a0 a1 (ae : inU0_eq Au Au a0 a1) b0 b1 (be : inU0_eq Au Au b0 b1), R a0 b0 <-> R a1 b1),
    extU0 A (cQuo A Au (inU0_eq Au Au) R).

Record U0@{i j} : Type@{j} :=
  mkU0 {
      El0 : Type@{i} ;
      in0 : inU0@{i j} El0 ;
      ext0 : extU0@{i j} El0 in0
  }.
Arguments mkU0 {_} {_}.

(* Even though its definition is somewhat complex, U0 is morally an inductive-recursive type.
   To allow for easier reasoning, we exhibit the IR interface of U0:
   - the functions El0, eq0 and eqU0
   - the constructors emb0, nat0, Prop0, Sigma0, Pi0, W0, Quo0
   - the induction principles U0_rect and U0_ind *)

Check (El0 : U0 -> Type).

Definition eq0 (A B : U0) (a : El0 A) (b : El0 B) : Prop :=
  inU0_eq (in0 A) (in0 B) a b.

Definition eqU0 (A B : U0) : Prop :=
  inU0_eqU (in0 A) (in0 B).

(* Constructors *)

Definition emb0 (P : Prop) : U0 := mkU0 (extEmb0 P).
Definition nat0 : U0 := mkU0 extN.
Definition Prop0 : U0 := mkU0 extProp.
Definition Sigma0 (A : U0) (B : El0 A -> U0) (Be : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (B a0) (B a1)) : U0 :=
  mkU0 (extSigma (El0 A) (in0 A) (ext0 A)
              (fun a => El0 (B a)) (fun a => in0 (B a))
              Be (fun a => ext0 (B a))).
Definition Pi0 (A : U0) (B : El0 A -> U0) (Be : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (B a0) (B a1)) : U0 :=
  mkU0 (extPi (El0 A) (in0 A) (ext0 A)
              (fun a => El0 (B a)) (fun a => in0 (B a))
              Be (fun a => ext0 (B a))).
Definition W0 (A : U0) (B : El0 A -> U0) (Be : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (B a0) (B a1)) : U0 :=
  mkU0 (extW (El0 A) (in0 A) (ext0 A)
             (fun a => El0 (B a)) (fun a => in0 (B a))
             Be (fun a => ext0 (B a))).
Definition Quo0 (A : U0) (R : El0 A -> El0 A -> Prop)
                (Re : forall a0 a1 (ae : eq0 A A a0 a1) b0 b1 (be : eq0 A A b0 b1), R a0 b0 <-> R a1 b1) : U0 :=
  mkU0 (extQuo (El0 A) (in0 A) (ext0 A) R Re).

(* Induction principles *)

Definition U0_rect@{i j k} (X : U0@{i j} -> Type@{k}) :
  forall (Xemb : forall (P : Prop), X (emb0 P))
         (Xnat : X nat0)
         (Xprop : X Prop0)
         (Xsigma : forall (A : U0) (IHA : X A) (P : El0 A -> U0) (IHP : forall a, X (P a))
                          (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1)), X (Sigma0 A P Pe))
         (Xpi : forall (A : U0) (IHA : X A) (P : El0 A -> U0) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1)), X (Pi0 A P Pe))
         (XW : forall (A : U0) (IHA : X A) (P : El0 A -> U0) (IHP : forall a, X (P a))
                      (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1)), X (W0 A P Pe))
         (Xquo : forall (A : U0) (IHA : X A) (R : El0 A -> El0 A -> Prop)
                      (Re : forall a0 a1 (ae : eq0 A A a0 a1) b0 b1 (be : eq0 A A b0 b1), R a0 b0 <-> R a1 b1), X (Quo0 A R Re))
         (A : U0), X A.
Proof.
  intros.
  destruct A as [A Au Ae].
  induction Ae as [ P | | | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA R Rext ].
  - exact (Xemb P).
  - exact Xnat.
  - exact Xprop.
  - exact (Xsigma (mkU0 Ae) IHA (fun a => mkU0 (Pe a)) IHP Pext).
  - exact (Xpi (mkU0 Ae) IHA (fun a => mkU0 (Pe a)) IHP Pext).
  - exact (XW (mkU0 Ae) IHA (fun a => mkU0 (Pe a)) IHP Pext).
  - exact (Xquo (mkU0 Ae) IHA R Rext).
Defined.

Definition U0_ind@{i j} (X : U0@{i j} -> Prop) :
  forall (Xemb : forall P, X (emb0 P))
         (Xnat : X nat0)
         (Xprop : X Prop0)
         (Xsigma : forall (A : U0) (IHA : X A) (P : El0 A -> U0) (IHP : forall a, X (P a))
                          (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1)), X (Sigma0 A P Pe))
         (Xpi : forall (A : U0) (IHA : X A) (P : El0 A -> U0) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1)), X (Pi0 A P Pe))
         (XW : forall (A : U0) (IHA : X A) (P : El0 A -> U0) (IHP : forall a, X (P a))
                      (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1)), X (W0 A P Pe))
         (Xquo : forall (A : U0) (IHA : X A) (R : El0 A -> El0 A -> Prop)
                      (Re : forall a0 a1 (ae : eq0 A A a0 a1) b0 b1 (be : eq0 A A b0 b1), R a0 b0 <-> R a1 b1), X (Quo0 A R Re))
         (A : U0), X A.
Proof.
  intros.
  destruct A as [A Au Ae].
  induction Ae as [ P | | | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA P Pu Pext Pe IHP | A Au Ae IHA R Rext ].
  - exact (Xemb P).
  - exact Xnat.
  - exact Xprop.
  - exact (Xsigma (mkU0 Ae) IHA (fun a => mkU0 (Pe a)) IHP Pext).
  - exact (Xpi (mkU0 Ae) IHA (fun a => mkU0 (Pe a)) IHP Pext).
  - exact (XW (mkU0 Ae) IHA (fun a => mkU0 (Pe a)) IHP Pext).
  - exact (Xquo (mkU0 Ae) IHA R Rext).
Defined.

(* Double induction principle:
   If we want to define something by induction on two elements A and B of U0, and we know that
   A and B are equal, then we only need to treat the diagonal cases. *)

Definition U0_rect2@{i j k} (X : forall (A B : U0@{i j}), eqU0 A B -> Type@{k}) :
  forall (Xemb : forall (P Q : Prop) (e : P <-> Q), X (emb0 P) (emb0 Q) e)
         (Xnat : X nat0 nat0 I)
         (Xprop : X Prop0 Prop0 I)
         (Xsigma : forall (A B : U0@{i j}) (eAB : eqU0 A B) (IHA : X A B eAB) (P : El0 A -> U0@{i j}) (Q : El0 B -> U0@{i j})
                       (ePQ : forall a b, eq0 A B a b -> eqU0 (P a) (Q b))
                       (IHP : forall a b (eab : eq0 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1))
                       (Qe : forall b0 b1 : El0 B, eq0 B B b0 b1 -> eqU0 (Q b0) (Q b1)),
             X (Sigma0 A P Pe) (Sigma0 B Q Qe) (conj eAB ePQ))
         (Xpi : forall (A B : U0@{i j}) (eAB : eqU0 A B) (IHA : X A B eAB) (P : El0 A -> U0@{i j}) (Q : El0 B -> U0@{i j})
                       (ePQ : forall a b, eq0 A B a b -> eqU0 (P a) (Q b))
                       (IHP : forall a b (eab : eq0 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1))
                       (Qe : forall b0 b1 : El0 B, eq0 B B b0 b1 -> eqU0 (Q b0) (Q b1)),
             X (Pi0 A P Pe) (Pi0 B Q Qe) (conj eAB ePQ))
         (XW : forall (A B : U0@{i j}) (eAB : eqU0 A B) (IHA : X A B eAB) (P : El0 A -> U0@{i j}) (Q : El0 B -> U0@{i j})
                      (ePQ : forall a b, eq0 A B a b -> eqU0 (P a) (Q b))
                      (IHP : forall a b (eab : eq0 A B a b), X (P a) (Q b) (ePQ a b eab))
                      (Pe : forall a0 a1 : El0 A, eq0 A A a0 a1 -> eqU0 (P a0) (P a1))
                      (Qe : forall b0 b1 : El0 B, eq0 B B b0 b1 -> eqU0 (Q b0) (Q b1)),
             X (W0 A P Pe) (W0 B Q Qe) (conj eAB ePQ))
         (Xquo : forall (A B : U0@{i j}) (eAB : eqU0 A B) (IHA : X A B eAB)
                        (R : El0 A -> El0 A -> Prop) (S : El0 B -> El0 B -> Prop)
                        (eRS : forall a0 b0 (e0 : eq0 A B a0 b0) a1 b1 (e1 : eq0 A B a1 b1), R a0 a1 <-> S b0 b1)
                        (Re : forall a0 a1 (ae : eq0 A A a0 a1) b0 b1 (be : eq0 A A b0 b1), R a0 b0 <-> R a1 b1)
                        (Se : forall a0 a1 (ae : eq0 B B a0 a1) b0 b1 (be : eq0 B B b0 b1), S a0 b0 <-> S a1 b1),
             X (Quo0 A R Re) (Quo0 B S Se) (conj eAB eRS))
         (A B : U0@{i j}) (e : eqU0 A B), X A B e.
Proof.
  intros Xemb Xnat Xprop Xsigma Xpi XW Xquo A.
  pattern A ; eapply U0_rect@{i j k}.
  - clear A. intros P B. pattern B ; eapply U0_rect@{i j k} ; try (now intros []).
    clear B. intros Q ePQ. exact (Xemb P Q ePQ).
  - intro B. pattern B ; eapply U0_rect@{i j k} ; try (now intros []) ; try easy.
  - intro B. pattern B ; eapply U0_rect@{i j k} ; try (now intros []) ; try easy.
  - clear A. intros A IHA P IHP Pe B. pattern B ; eapply U0_rect@{i j k} ; try (now intros []) ; try easy.
    clear B. intros B _ Q _ Qe [eAB ePQ]. eapply Xsigma.
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
  - clear A. intros A IHA P IHP Pe B. pattern B ; eapply U0_rect@{i j k} ; try (now intros []) ; try easy.
    clear B. intros B _ Q _ Qe [eAB ePQ]. eapply Xpi.
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
  - clear A. intros A IHA P IHP Pe B. pattern B ; eapply U0_rect@{i j k} ; try (now intros []) ; try easy.
    clear B. intros B _ Q _ Qe [eAB ePQ]. eapply XW.
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
  - clear A. intros A IHA R Re B. pattern B ; eapply U0_rect@{i j k} ; try (now intros []) ; try easy.
    clear B. intros B _ S Se [eAB eRS]. eapply Xquo.
    exact (IHA B eAB).
Defined.
