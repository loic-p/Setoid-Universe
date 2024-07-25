(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the definition of a type U0 of small setoids and a type U1 of large setoids.
   Both universes are closed under Pi-types, Sigma-types, W-types, and quotient types.
   Additionally, U0 contains the setoid of propositions and the setoid of natural numbers,
   and U1 contains U0 and an embedding from U0 into U1. *)

(* Both universes are equipped with a setoid equality between their elements, as well as a
   heterogeneous observational equality between the elements of their elements.
   Both equalities are reflexive, transitive and symmetric, and there is a cast operator. *)

(* In the second part of this file, we use these universes to do a shallow embedding of an
   observational type theory that supports (propositional) proof irrelevance, function
   extensionality, proposition extensionality, impredicative propositions, large elimination of the
   accessibility predicate, and quotient types.
   In other words, we have the full CIC augmented with extensionality principles. *)

Set Universe Polymorphism.
Set Primitive Projections.

(* We start with definitions of useful datatypes and lemmas *)

Inductive nat : Type@{Set} :=
| zero : nat
| suc : nat -> nat.

Inductive empty : Type@{Set} :=.

Inductive unit : Type@{Set} :=
| tt : unit.

Inductive nateq : nat -> nat -> Prop :=
| eqzero : nateq zero zero
| eqsuc : forall (n m : nat), nateq n m -> nateq (suc n) (suc m).

Definition nateq_ind_ex : forall (P : forall n m, nateq n m -> Prop),
    P zero zero eqzero -> (forall (n m : nat) (e : nateq n m), P n m e -> P (suc n) (suc m) (eqsuc n m e)) -> forall (n m : nat) (e : nateq n m), P n m e.
Proof.
  intros P Pz Ps.
  exact (fix F (n m : nat) (e : nateq n m) {struct e} : P n m e :=
           match e in (nateq n m) return (P n m e) with
           | eqzero => Pz
           | eqsuc n0 m0 e0 => Ps n0 m0 e0 (F n0 m0 e0)
           end).
Defined.

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

Record Sigma@{i j} (A : Type@{i}) (B : A -> Type@{j}) : Type@{max(i,j)} :=
  mkPair {
    fst : A;
    snd : B fst;
  }.
Arguments mkPair {_} {_}.
Arguments fst {_} {_}.
Arguments snd {_} {_}.

Record and_ex (A B : Prop) : Prop :=
  mkAndEx {
    andleft : A;
    andright : B;
  }.

Arguments mkAndEx {_} {_}.
Arguments andleft {_} {_}.
Arguments andright {_} {_}.

Inductive W@{i} (A : Type@{i}) (B : A -> Type@{i}) : Type@{i} :=
| sup : forall (a : A) (f : B a -> W A B), W A B.

Arguments sup {_} {_}.

Inductive Weq@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> Prop)
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Prop)
  : W A0 B0 -> W A1 B1 -> Prop :=
| eqsup : forall (a0 : A0) (a1 : A1) (ae : Aeq a0 a1)
                 (f0 : forall (b0 : B0 a0), W A0 B0) (f1 : forall (b1 : B1 a1), W A1 B1)
                 (fe : forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1))
  , Weq Aeq Beq (sup a0 f0) (sup a1 f1).

Arguments eqsup {_} {_} {_} {_} {_} {_}.

Definition Weq_step@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> Prop)
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Prop)
  (w0 : W A0 B0) (w1 : W A1 B1) : Prop :=
  match w0 with
  | sup a0 f0 => match w1 with
                 | sup a1 f1 => Aeq a0 a1 /\ forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1)
                 end
  end.

Definition Weq_step_lemma@{i} {A0 A1 : Type@{i}} (Aeq : A0 -> A1 -> Prop)
  {B0 : A0 -> Type@{i}} {B1 : A1 -> Type@{i}} (Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Prop)
  (w0 : W A0 B0) (w1 : W A1 B1) (we : Weq Aeq Beq w0 w1) : Weq_step Aeq Beq w0 w1.
Proof.
  destruct we as [ a0 a1 ae f0 f1 fe ].
  now split.
Defined.

Definition Weq_inversion {A0 A1 : Type} {Aeq : A0 -> A1 -> Prop}
  {B0 : A0 -> Type} {B1 : A1 -> Type} {Beq : forall (a0 : A0) (a1 : A1), B0 a0 -> B1 a1 -> Prop}
  {a0 : A0} {a1 : A1} {f0 : forall (b0 : B0 a0), W A0 B0} {f1 : forall (b1 : B1 a1), W A1 B1}
  : Weq Aeq Beq (sup a0 f0) (sup a1 f1) -> Aeq a0 a1 /\ forall (b0 : B0 a0) (b1 : B1 a1) (be : Beq a0 a1 b0 b1), Weq Aeq Beq (f0 b0) (f1 b1).
Proof.
  intro e. apply (Weq_step_lemma Aeq Beq _ _) in e. exact e.
Defined.

Inductive Wext@{i} (A : Type@{i}) (Aeq : A -> A -> Prop)
  (B : A -> Type@{i}) (Beq : forall a0 a1 : A, B a0 -> B a1 -> Prop) : W A B -> Type@{i} :=
| extsup : forall (a : A)
                  (f : forall (b : B a), W A B)
                  (fe : forall (b : B a), Wext A Aeq B Beq (f b))
                  (fext : forall (b0 b1 : B a) (be : Beq a a b0 b1), Weq Aeq Beq (f b0) (f b1))
  , Wext A Aeq B Beq (sup a f).

Arguments extsup {_} {_} {_} {_}.

Inductive Acc@{i} (A : Type@{i}) (R : A -> A -> Prop) (a : A) : Prop :=
| acc : (forall (b : A), R b a -> Acc A R b) -> Acc A R a.

Definition Acc_rect_ex (A : Type) (R : A -> A -> Prop) (P : forall (a : A), Acc A R a -> Type)
  (IH : forall (a : A) (HRa : forall b : A, R b a -> Acc A R b), (forall (b : A) (Hb : R b a), P b (HRa b Hb)) -> P a (acc A R a HRa))
  (a : A) (Ha : Acc A R a) : P a Ha.
  exact ((fix F (a : A) (Ha : Acc A R a) {struct Ha} : P a Ha :=
           match Ha return P a Ha with
           | acc _ _ _ HRa => IH a HRa (fun b Hb => F b (HRa b Hb))
           end) a Ha).
Defined.

(* Reflective, symmetric, transitive closure of a relation R on a setoid whose equality is eA *)
Inductive closure {A : Type} (eA : A -> A -> Prop) (R : A -> A -> Prop) : A -> A -> Prop :=
| clo_emb : forall a b, R a b -> closure eA R a b
| clo_refl : forall a b, eA a b -> closure eA R a b
| clo_sym : forall a b, closure eA R a b -> closure eA R b a
| clo_trans : forall a b c, closure eA R a b -> closure eA R b c -> closure eA R a c.

(* The universe U0 will be defined in three steps:

   - First, we define the indexed datatype inU0 that encodes the graph of the El0 function.
     Since elements of Pi-types and W-types need to be extensional, but we do not have access
     to the equalities yet (no induction-recursion!), we parameterize them with some arbitrary
     notion of equality.

   - Second, we define the two equalities on inU0

   - Third, we define the datatype extU0 indexed over inU0, which ensures that the arbitrary
     equality contained in Pi-types and W-types matches the actual equality that we defined in
     step 2

   - Finally, we define an inhabitant of U0 as a small type A, a proof A' that it is inU0, and
     a proof A'' that the pair (A, A') is in extU0. *)

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

(* We redefine the equalities on U0 *)

Definition eq0 (A B : U0) (a : El0 A) (b : El0 B) : Prop :=
  inU0_eq (in0 A) (in0 B) a b.

Definition eqU0 (A B : U0) : Prop :=
  inU0_eqU (in0 A) (in0 B).

(* Even though its definition is somewhat complex, U0 is morally an inductive type.
   To reason more easily, we define constructors for U0 and induction principles. *)

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

(* Now, we show that the equalities are reflexive and symmetric, as an application
   of our induction principles. *)

Definition refl0 (A : U0) (a : El0 A) : eq0 A A a a.
Proof.
  revert a. pattern A ; eapply U0_ind.
  - easy.
  - exact nateq_refl.
  - exact iff_refl.
  - clear A. intros A IHA P IHP Pext [ a p ]. split.
    + exact (IHA a).
    + exact (IHP a p).
  - clear A. intros A IHA P IHP Pext [ f fe ]. exact fe.
  - clear A. intros A IHA P IHP Pext [ w we ]. induction we as [ a f fe IHf fext ]. econstructor.
    + exact (IHA a).
    + intros b0 b1 be. exact (fext b0 b1 be).
  - clear A. intros A IHA R Re a. exists a. exists a. split.
    + eapply clo_refl. eapply IHA.
    + split. eapply IHA. eapply clo_refl. eapply IHA.
Defined.

Definition reflU0 (A : U0) : eqU0 A A.
Proof.
  pattern A ; eapply U0_ind ; now econstructor.
Defined.

Definition sym0_pre (A B : U0) {a : El0 A} {b : El0 B} : eq0 A B a b <-> eq0 B A b a.
Proof.
  revert B a b. pattern A ; eapply U0_ind ; clear A.
  - intros P B ; pattern B ; eapply U0_ind ; clear B.
    2,3,4,5,6,7: intros ; split ; now intros [].
    intros Q p q. easy.
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,3,4,5,6,7: intros ; split ; now intros [].
    intros a b. split ; exact nateq_sym.
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,4,5,6,7: intros ; split ; now intros [].
    intros a b. split ; now apply iff_sym.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,5,6,7: intros ; split ; now intros [].
    intros B _ Q _ Qe t u. split.
    + intros [ eap epq ]. split.
      * apply IHA. exact eap.
      * apply IHP. exact epq.
    + intros [ eap epq ]. split.
      * apply IHA. exact eap.
      * apply IHP. exact epq.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,6,7: intros ; split ; now intros [].
    intros B _ Q _ Qe f g. split.
    + intros e b a eba. eapply IHP. apply <- IHA in eba. exact (e a b eba).
    + intros e a b eab. eapply IHP. apply IHA in eab. exact (e b a eab).
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,7: intros ; split ; now intros [].
    intros B _ Q _ Qe.
    change (forall (w0 : El0 (W0 A P Pe)) (w1 : El0 (W0 B Q Qe)),
               (Weq (eq0 A B) (fun a b => eq0 (P a) (Q b)) (fst w0) (fst w1))
               <-> (Weq (eq0 B A) (fun b a => eq0 (Q b) (P a)) (fst w1) (fst w0))).
    intros [ w0 w0e ] [ w1 w1e ]. simpl.
    clear w0e w1e. split.
    + intros e. induction e as [ a b eab f g efg IH ]. constructor.
      * apply (IHA B a b). exact eab.
      * intros q p eqp. unshelve eapply (IH p q _).
        eapply IHP. exact eqp.
    + intros e. induction e as [ b a eba g f egf IH ]. constructor.
      * apply (IHA B a b). exact eba.
      * intros p q epq. unshelve eapply (IH q p _).
        eapply IHP. exact epq.
  - intros A IHA R Re. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,6: intros ; split ; now intros [].
    intros B _ S Se. intros a b. split.
    + intros [ a1 [ b1 [ ae [ e be ] ] ] ].
      exists b1. exists a1. split. exact (clo_sym _ S _ _ be).
      split. apply (IHA B a1 b1). exact e. exact (clo_sym _ R _ _ ae).
    + intros [ b1 [ a1 [ be [ e ae ] ] ] ].
      exists a1. exists b1. split. exact (clo_sym _ R _ _ ae).
      split. apply (IHA B a1 b1). exact e. exact (clo_sym _ S _ _ be).
Defined.

Definition sym0 (A B : U0) {a : El0 A} {b : El0 B} : eq0 A B a b -> eq0 B A b a.
Proof.
  intro e. eapply (sym0_pre A B). exact e.
Defined.

Definition symU0_pre (A B : U0) : eqU0 A B <-> eqU0 B A.
Proof.
  revert B. pattern A ; eapply U0_ind ; clear A.
  - intro P. intro B ; pattern B ; eapply U0_ind ; clear B.
    2,3,4,5,6,7: split ; now intros [].
    intro Q. split ; eapply iff_sym.
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,3,4,5,6,7: split ; now intros [].
    easy.
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,4,5,6,7: split ; now intros [].
    easy.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,5,6,7: split ; now intros [].
    intros B _ Q _ Qe. split.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,6,7: split ; now intros [].
    intros B _ Q _ Qe. split.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,7: split ; now intros [].
    intros B _ Q _ Qe. split.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
  - intros A IHA R Re. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,6: split ; now intros [].
    intros B _ S Se. split.
    + intros [ eAB eRS ]. apply IHA in eAB. econstructor.
      exact eAB. intros a0 b0 e0 a1 b1 e1. eapply iff_sym. eapply eRS.
      now eapply sym0. now eapply sym0.
    + intros [ eBA eSR ]. apply IHA in eBA. econstructor.
      exact eBA. intros a0 b0 e0 a1 b1 e1. eapply iff_sym. eapply eSR.
      now eapply sym0. now eapply sym0.
Defined.

Definition symU0 (A B : U0) : eqU0 A B -> eqU0 B A.
Proof.
  intro e. eapply (symU0_pre A B). exact e.
Defined.

(* Now we want to prove transitivity. That one is a bit more difficult, because it
   needs to be defined mutually with a typecasting functions.
   In fact, we define 6 mutual properties for pairs of equal types: transitivity in
   both directions, cast in both directions, and heterogeneous equality between x
   and cast(x) in both directions. *)

Set Implicit Arguments.

Record cast_lemmas_conclusion@{i j} (A : U0@{i j}) (B : U0@{i j}) (e : eqU0 A B) : Type@{i} :=
  {
    transf : forall (C : U0@{i j}) {a b c} (eab : eq0 A B a b) (ebc : eq0 B C b c), eq0 A C a c ;
    transb : forall (C : U0@{i j}) {a b c} (eab : eq0 B A b a) (ebc : eq0 A C a c), eq0 B C b c ;
    castf : El0 A -> El0 B ;
    castb : El0 B -> El0 A ;
    castf_eq : forall (a : El0 A), eq0 A B a (castf a) ;
    castb_eq : forall (b : El0 B), eq0 B A b (castb b) ;
  }.

Unset Implicit Arguments.

(* auxiliary lemmas for typecasting between W-types *)

Lemma Wcast (A B : U0) (castAB : El0 A -> El0 B) (castABe : forall a, eq0 A B a (castAB a))
  (P : El0 A -> U0) (Q : El0 B -> U0) (castPQ : forall (a : El0 A) (b : El0 B), eq0 A B a b -> El0 (Q b) -> El0 (P a)) :
  W (El0 A) (fun a => El0 (P a)) -> W (El0 B) (fun b => El0 (Q b)).
Proof.
  intro w0. induction w0 as [ a f IHf ].
  exact (sup (castAB a) (fun q => IHf (castPQ a (castAB a) (castABe a) q))).
Defined.

Lemma Wcast_eq (A B : U0) (castAB : El0 A -> El0 B) (castABe : forall a, eq0 A B a (castAB a))
  (castAB_eq : forall a0 a1, eq0 A A a0 a1 -> eq0 B B (castAB a0) (castAB a1))
  (P : El0 A -> U0) (Q : El0 B -> U0) (castPQ : forall (a : El0 A) (b : El0 B), eq0 A B a b -> El0 (Q b) -> El0 (P a))
  (castPQ_eq : forall a0 b0 e0 a1 b1 e1 q0 q1, eq0 (Q b0) (Q b1) q0 q1 -> eq0 (P a0) (P a1) (castPQ a0 b0 e0 q0) (castPQ a1 b1 e1 q1))
  (w0 w1 : W (El0 A) (fun a => El0 (P a))) (we : Weq (eq0 A A) (fun a0 a1 => eq0 (P a0) (P a1)) w0 w1)
  : Weq (eq0 B B) (fun b0 b1 => eq0 (Q b0) (Q b1)) (Wcast A B castAB castABe P Q castPQ w0) (Wcast A B castAB castABe P Q castPQ w1).
Proof.
  induction we as [ a0 a1 ae f0 f1 fe IH ]. simpl.
  refine (eqsup (castAB a0) (castAB a1) _
                (fun q => Wcast A B castAB castABe P Q castPQ (f0 (castPQ a0 (castAB a0) (castABe a0) q)))
                (fun q => Wcast A B castAB castABe P Q castPQ (f1 (castPQ a1 (castAB a1) (castABe a1) q)))
                _).
  - now apply castAB_eq.
  - intros q0 q1 qe. unshelve eapply (IH (castPQ _ _ (castABe a0) q0) (castPQ _ _ (castABe a1) q1) _).
    now apply castPQ_eq.
Defined.

(* auxiliary lemmas for transitivity between quotient types *)

Definition closure_eqrel (A B : U0) (eAB : eqU0 A B) (IH : cast_lemmas_conclusion A B eAB)
  (R : El0 A -> El0 A -> Prop) (S : El0 B -> El0 B -> Prop)
  (Re : forall a0 a1 (ae : eq0 A A a0 a1) b0 b1 (be : eq0 A A b0 b1), R a0 b0 <-> R a1 b1)
  (Se : forall a0 a1 (ae : eq0 B B a0 a1) b0 b1 (be : eq0 B B b0 b1), S a0 b0 <-> S a1 b1)
  (eRS : forall a0 b0 (e0 : eq0 A B a0 b0) a1 b1 (e1 : eq0 A B a1 b1), R a0 a1 <-> S b0 b1)
  : forall a0 b0 (e0 : eq0 A B a0 b0) a1 b1 (e1 : eq0 A B a1 b1), closure (eq0 A A) R a0 a1 <-> closure (eq0 B B) S b0 b1.
Proof.
  intros a0 b0 e0 a1 b1 e1. split.
  - intro Ha. revert b0 e0 b1 e1. induction Ha.
    + intros b0 e0 b1 e1. eapply clo_emb. eapply (eRS a b0 e0 b b1 e1). exact H.
    + intros b0 e0 b1 e1. pose proof (transb IH B (transb IH A (sym0 _ _ e0) H) e1) as be.
      eapply clo_refl. exact be.
    + intros b0 e0 b1 e1. eapply clo_sym. eapply IHHa. exact e1. exact e0.
    + intros b0 e0 b1 e1. set (b2 := castf IH b). eapply (clo_trans _ _ b0 b2 b1).
      * eapply (IHHa1 b0 e0 b2). exact (castf_eq IH b).
      * unshelve eapply (IHHa2 b2 _ b1 e1). exact (castf_eq IH b).
  - intro Hb. revert a0 e0 a1 e1. induction Hb.
    + intros a0 e0 a1 e1. eapply clo_emb. eapply (eRS a0 a e0 a1 b e1). exact H.
    + intros a0 e0 a1 e1. pose proof (transf IH A (transf IH B e0 H) (sym0 _ _ e1)) as ae.
      eapply clo_refl. exact ae.
    + intros a0 e0 a1 e1. eapply clo_sym. eapply IHHb. exact e1. exact e0.
    + intros a0 e0 a1 e1. set (a2 := castb IH b). eapply (clo_trans _ _ a0 a2 a1).
      * eapply (IHHb1 a0 e0 a2). exact (sym0 _ _ (castb_eq IH b)).
      * unshelve eapply (IHHb2 a2 _ a1 e1). exact (sym0 _ _ (castb_eq IH b)).
Defined.

Definition cast_lemmas@{i j} (A : U0@{i j}) (B : U0@{i j}) (e : eqU0 A B) : cast_lemmas_conclusion@{i j} A B e.
Proof.
  eapply U0_rect2 ; clear A B e.
  (* emb *)
  - unshelve econstructor.
    + eapply e.
    + eapply e.
    + intro C. pattern C ; eapply U0_ind ; clear C ; easy.
    + intro C. pattern C ; eapply U0_ind ; clear C ; easy.
    + easy.
    + easy.
  (* nat *)
  - unshelve econstructor.
    + exact (fun n => n).
    + exact (fun n => n).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros a b c. eapply nateq_trans.
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros a b c. eapply nateq_trans.
    + eapply nateq_refl.
    + eapply nateq_refl.
  (* Prop *)
  - unshelve econstructor.
    + exact (fun P => P).
    + exact (fun P => P).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros a b c. eapply iff_trans.
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros a b c. eapply iff_trans.
    + eapply iff_refl.
    + eapply iff_refl.
  (* Sigma *)
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. unshelve econstructor.
    + intros [ a p ]. econstructor.
      exact (castf (IHP _ _ (castf_eq IHA a)) p).
    + intros [ b q ]. econstructor.
      exact (castb (IHP _ _ (sym0 _ _ (castb_eq IHA b))) q).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ R _ Re [ a p ] [ b q ] [ c r ] [ eab epq ] [ ebc eqr ]. econstructor.
      * exact (transf IHA C eab ebc).
      * exact (transf (IHP a b eab) (R c) epq eqr).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ R _ Re [ a p ] [ b q ] [ c r ] [ eba eqp ] [ eac epr ]. econstructor.
      * exact (transb IHA C eba eac).
      * exact (transb (IHP a b (sym0 _ _ eba)) (R c) eqp epr).
    + intros [ a p ]. econstructor.
      * exact (castf_eq IHA a).
      * exact (castf_eq (IHP _ _ (castf_eq IHA a)) p).
    + intros [ b q ]. econstructor.
      * exact (castb_eq IHA b).
      * exact (castb_eq (IHP _ _ (sym0 _ _ (castb_eq IHA b))) q).
  (* Pi *)
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. unshelve econstructor.
    + intros [ f fe ]. change (forall a0 a1, eq0 A A a0 a1 -> eq0 (P a0) (P a1) (f a0) (f a1)) in fe. unshelve econstructor.
      * refine (fun b => castf (IHP _ _ (sym0 B A (castb_eq IHA b))) (f (castb IHA b))).
      * intros b0 b1 eb. change (eq0 B B b0 b1) in eb. cbn.
        pose proof (transf IHA B (sym0 B A (castb_eq IHA b1)) (sym0 B B eb)) as e0.
        pose proof (transf IHA A (sym0 B A (castb_eq IHA b0)) (sym0 A B e0)) as e1.
        pose proof (fe _ _ e1) as e2.
        pose proof (castf_eq (IHP _ _ (sym0 B A (castb_eq IHA b1))) (f (castb IHA b1))) as e3.
        pose proof (castf_eq (IHP _ _ (sym0 B A (castb_eq IHA b0))) (f (castb IHA b0))) as e4.
        pose proof (transb (IHP _ _ (sym0 B A (castb_eq IHA b0))) (P (castb IHA b1)) (sym0 _ _ e4) e2) as e5.
        exact (transb (IHP _ _ e0) (Q b1) e5 e3).
    + intros [ f fe ]. change (forall b0 b1, eq0 B B b0 b1 -> eq0 (Q b0) (Q b1) (f b0) (f b1)) in fe. unshelve econstructor.
      * refine (fun a => castb (IHP _ _ (castf_eq IHA a)) (f (castf IHA a))).
      * intros a0 a1 ea. change (eq0 A A a0 a1) in ea. cbn.
        pose proof (transb IHA A (sym0 A B (castf_eq IHA a0)) ea) as e0.
        pose proof (transb IHA B e0 (castf_eq IHA a1)) as e1.
        pose proof (fe _ _ e1) as e2.
        pose proof (castb_eq (IHP _ _ (castf_eq IHA a0)) (f (castf IHA a0))) as e3.
        pose proof (castb_eq (IHP _ _ (castf_eq IHA a1)) (f (castf IHA a1))) as e4.
        pose proof (transf (IHP _ _ (castf_eq IHA a1)) (Q (castf IHA a0)) (sym0 _ _ e4) (sym0 _ _ e2)) as e5.
        exact (sym0 _ _ (transf (IHP _ _ (sym0 B A e0)) (P a0) e5 e3)).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ R _ Re f g h efg egh a c eac. change (eq0 A C a c) in eac.
      set (b := castf IHA a).
      pose proof (castf_eq IHA a) as eab. change (eq0 A B a b) in eab.
      pose proof (transb IHA C (sym0 A B eab) eac) as ebc.
      exact (transf (IHP a b eab) (R c) (efg _ _ eab) (egh _ _ ebc)).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ R _ Re f g h egf efh b c ebc. change (eq0 B C b c) in ebc.
      set (a := castb IHA b).
      pose proof (castb_eq IHA b) as eba. change (eq0 B A b a) in eba.
      pose proof (transf IHA C (sym0 B A eba) ebc) as eac.
      exact (transb (IHP a b (sym0 B A eba)) (R c) (egf _ _ eba) (efh _ _ eac)).
    + intros [ f fe ] a b eab. change (eq0 A B a b) in eab.
      pose proof (transf IHA A eab (castb_eq IHA b)) as e0.
      pose proof (fe _ _ e0) as e1. change (eq0 (P a) (P (castb IHA b)) (f a) (f (castb IHA b))) in e1.
      pose proof (castf_eq (IHP _ _ (sym0 B A (castb_eq IHA b))) (f (castb IHA b))) as e2.
      exact (sym0 _ _ (transb (IHP _ _ (sym0 B A (castb_eq IHA b))) (P a) (sym0 _ _ e2) (sym0 _ _ e1))).
    + intros [ f fe ] b a eba. change (eq0 B A b a) in eba.
      pose proof (transb IHA B eba (castf_eq IHA a)) as e0.
      pose proof (fe _ _ e0) as e1. change (eq0 (Q b) (Q (castf IHA a)) (f b) (f (castf IHA a))) in e1.
      pose proof (castb_eq (IHP _ _ (castf_eq IHA a)) (f (castf IHA a))) as e2.
      exact (sym0 _ _ (transf (IHP _ _ (castf_eq IHA a)) (Q b) (sym0 _ _ e2) (sym0 _ _ e1))).
  (* W *)
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. unshelve econstructor.
    + intros [ w we ]. unshelve econstructor.
      * exact (Wcast A B (castf IHA) (castf_eq IHA) P Q (fun a b eab => castb (IHP a b eab)) w).
      * induction we as [ a f fe IHf fext ]. simpl.
        refine (extsup (castf IHA a)
                  (fun q => Wcast A B (castf IHA) (castf_eq IHA) P Q (fun a b eab => castb (IHP a b eab))
                              (f (castb (IHP _ _ (castf_eq IHA a)) q)))
                  (fun q => IHf (castb (IHP _ _ (castf_eq IHA a)) q)) _).
        intros q0 q1 qe.
        unshelve refine (Wcast_eq A B (castf IHA) (castf_eq IHA) _ P Q (fun a b eab => castb (IHP a b eab)) _
                           (f (castb (IHP a (castf IHA a) (castf_eq IHA a)) q0))
                           (f (castb (IHP a (castf IHA a) (castf_eq IHA a)) q1))
                           _).
        ** clear a f fe IHf fext q0 q1 qe. intros a0 a1 ae.
           pose proof (transb IHA A (sym0 _ _ (castf_eq IHA a0)) ae) as e0.
           exact (transb IHA B e0 (castf_eq IHA a1)).
        ** clear a f fe IHf fext q0 q1 qe. intros a0 b0 e0 a1 b1 e1 q0 q1 qe.
           pose proof (sym0 _ _ (transf (IHP a0 b0 e0) (Q b1) (sym0 _ _ (castb_eq (IHP a0 b0 e0) q0)) qe)) as e2.
           pose proof (sym0 _ _ (castb_eq (IHP a1 b1 e1) q1)) as e3.
           exact (sym0 _ _ (transf (IHP a1 b1 e1) (P a0) e3 e2)).
        ** eapply fext. clear f fe IHf fext.
           pose proof (sym0 _ _ (transf (IHP _ _ (castf_eq IHA a)) _ (sym0 _ _ (castb_eq (IHP _ _ (castf_eq IHA a)) q0)) qe)) as e2.
           pose proof (sym0 _ _ (castb_eq (IHP _ _ (castf_eq IHA a)) q1)) as e3.
           exact (sym0 _ _ (transf (IHP _ _ (castf_eq IHA a)) (P a) e3 e2)).
    + intros [ w we ]. unshelve econstructor.
      * exact (Wcast B A (castb IHA) (castb_eq IHA) Q P (fun b a eba => castf (IHP a b (sym0 _ _ eba))) w).
      * induction we as [ b f fe IHf fext ]. simpl.
        refine (extsup (castb IHA b)
                  (fun p => Wcast B A (castb IHA) (castb_eq IHA) Q P (fun b a eba => castf (IHP a b (sym0 _ _ eba)))
                              (f (castf (IHP _ _ (sym0 _ _ (castb_eq IHA b))) p)))
                  (fun p => IHf (castf (IHP _ _ (sym0 _ _ (castb_eq IHA b))) p)) _).
        intros p0 p1 pe.
        unshelve refine (Wcast_eq B A (castb IHA) (castb_eq IHA) _ Q P (fun b a eba => castf (IHP a b (sym0 _ _ eba))) _
                           (f (castf (IHP _ _ (sym0 _ _ (castb_eq IHA b))) p0))
                           (f (castf (IHP _ _ (sym0 _ _ (castb_eq IHA b))) p1))
                           _).
        ** clear b f fe IHf fext p0 p1 pe. intros b0 b1 be.
           pose proof (transf IHA B (sym0 _ _ (castb_eq IHA b0)) be) as e0.
           exact (transf IHA A e0 (castb_eq IHA b1)).
        ** clear b f fe IHf fext p0 p1 pe. intros b0 a0 e0 b1 a1 e1 p0 p1 pe.
           pose proof (sym0 _ _ (transb (IHP a0 b0 (sym0 _ _ e0)) (P a1) (sym0 _ _ (castf_eq (IHP a0 b0 (sym0 _ _ e0)) p0)) pe)) as e2.
           pose proof (sym0 _ _ (castf_eq (IHP a1 b1 (sym0 _ _ e1)) p1)) as e3.
           exact (sym0 _ _ (transb (IHP a1 b1 (sym0 _ _ e1)) (Q b0) e3 e2)).
        ** eapply fext. clear f fe IHf fext.
           pose proof (sym0 _ _ (transb (IHP _ _ (sym0 _ _ (castb_eq IHA b))) _
                                   (sym0 _ _ (castf_eq (IHP _ _ (sym0 _ _ (castb_eq IHA b))) p0)) pe)) as e2.
           pose proof (sym0 _ _ (castf_eq (IHP _ _ (sym0 _ _ (castb_eq IHA b))) p1)) as e3.
           exact (sym0 _ _ (transb (IHP _ _ (sym0 _ _ (castb_eq IHA b))) (Q b) e3 e2)).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ R _ Re [ w we ] [ x xe ] [ y ye ].
      change ((Weq (eq0 A B) (fun a b => eq0 (P a) (Q b)) w x) -> (Weq (eq0 B C) (fun b c => eq0 (Q b) (R c)) x y)
              -> (Weq (eq0 A C) (fun a c => eq0 (P a) (R c)) w y)) ; clear we xe ye.
      intro ewx ; revert y. induction ewx as [ a b eab f g efg IH ].
      intros y exy. destruct y as [ c h ]. apply Weq_inversion in exy. destruct exy as [ ebc egh ].
      refine (eqsup a c (transf IHA C eab ebc) f h _).
      intros p r epr. set (q := castf (IHP a b eab) p).
      pose proof (castf_eq (IHP a b eab) p) as epq. change (eq0 (P a) (Q b) p q) in epq.
      refine (IH p q epq (h r) _). refine (egh q r _).
      exact (transb (IHP a b eab) (R c) (sym0 _ _ epq) epr).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ R _ Re [ w we ] [ x xe ] [ y ye ].
      change ((Weq (eq0 B A) (fun b a => eq0 (Q b) (P a)) x w) -> (Weq (eq0 A C) (fun a c => eq0 (P a) (R c)) w y)
              -> (Weq (eq0 B C) (fun b c => eq0 (Q b) (R c)) x y)) ; clear we xe ye.
      intro exw ; revert y. induction exw as [ b a eba g f egf IH ].
      intros y ewy. destruct y as [ c h ]. apply Weq_inversion in ewy. destruct ewy as [ eac efh ].
      refine (eqsup b c (transb IHA C eba eac) g h _).
      intros q r eqr. set (p := castb (IHP a b (sym0 _ _ eba)) q).
      pose proof (castb_eq (IHP a b (sym0 _ _ eba)) q) as eqp. change (eq0 (Q b) (P a) q p) in eqp.
      refine (IH q p eqp (h r) _). refine (efh p r _).
      exact (transf (IHP a b (sym0 _ _ eba)) (R c) (sym0 _ _ eqp) eqr).
    + intros [ w we ].
      change (Weq (eq0 A B) (fun a b => eq0 (P a) (Q b)) w (Wcast A B (castf IHA) (castf_eq IHA) P Q (fun a b eab => castb (IHP a b eab)) w)).
      assert (forall x, Weq (eq0 A A) (fun a0 a1 => eq0 (P a0) (P a1)) w x
                        -> Weq (eq0 A B) (fun a b => eq0 (P a) (Q b)) w
                             (Wcast A B (castf IHA) (castf_eq IHA) P Q (fun a b eab => castb (IHP a b eab)) x)) as Hgen.
      { clear we. intros x ewx.
        induction ewx as [ a0 a1 ae f0 f1 fe IH ]. constructor.
        - exact (sym0 _ _ (transb IHA A (sym0 _ _ (castf_eq IHA a1)) (sym0 _ _ ae))).
        - intros p q epq. refine (IH p (castb (IHP _ _ (castf_eq IHA a1)) q) _).
          pose proof (castb_eq (IHP _ _ (castf_eq IHA a1)) q) as e0.
          exact (sym0 _ _ (transf (IHP _ _ (castf_eq IHA a1)) (P a0) (sym0 _ _ e0) (sym0 _ _ epq))). }
      exact (Hgen w (refl0 (W0 A P Pe) {| fst := w ; snd := we |})).
    + intros [ w we ].
      change (Weq (eq0 B A) (fun b a => eq0 (Q b) (P a)) w
                (Wcast B A (castb IHA) (castb_eq IHA) Q P (fun b a eba => castf (IHP a b (sym0 _ _ eba))) w)).
      assert (forall x, Weq (eq0 B B) (fun b0 b1 => eq0 (Q b0) (Q b1)) w x
                        -> Weq (eq0 B A) (fun b a => eq0 (Q b) (P a)) w
                             (Wcast B A (castb IHA) (castb_eq IHA) Q P (fun b a eba => castf (IHP a b (sym0 _ _ eba))) x)) as Hgen.
      { clear we. intros x ewx.
        induction ewx as [ b0 b1 be f0 f1 fe IH ]. constructor.
        - exact (sym0 _ _ (transf IHA B (sym0 _ _ (castb_eq IHA b1)) (sym0 _ _ be))).
        - intros q p eqp. refine (IH q (castf (IHP _ _ (sym0 _ _ (castb_eq IHA b1))) p) _).
          pose proof (castf_eq (IHP _ _ (sym0 _ _ (castb_eq IHA b1))) p) as e0.
          exact (sym0 _ _ (transb (IHP _ _ (sym0 _ _ (castb_eq IHA b1))) (Q b0) (sym0 _ _ e0) (sym0 _ _ eqp))). }
      exact (Hgen w (refl0 (W0 B Q Qe) {| fst := w ; snd := we |})).
  (* Quotients *)
  - intros A B eAB IHA R S eRS Re Se. unshelve econstructor.
    + exact (castf IHA).
    + exact (castb IHA).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ T Te a b c [ a1 [ b1 [ ae [ eab be1 ] ] ] ] [ b2 [ c1 [ be2 [ ebc ce ] ] ] ].
      exists (castb IHA b2). exists c1. split.
      * refine (clo_trans _ R _ _ _ ae _).
        apply (closure_eqrel A B eAB IHA R S Re Se eRS a1 b1 eab (castb IHA b2) b2 (sym0 _ _ (castb_eq IHA b2))).
        exact (clo_trans _ S _ _ _ be1 be2).
      * split. refine (transf IHA C _ ebc). apply sym0. exact (castb_eq IHA b2). exact ce.
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ T Te a b c [ b1 [ a1 [ be [ eab ae1 ] ] ] ] [ a2 [ c1 [ ae2 [ eac ce ] ] ] ].
      exists (castf IHA a2). exists c1. split.
      * refine (clo_trans _ S _ _ _ be _).
        apply (closure_eqrel A B eAB IHA R S Re Se eRS a1 b1 (sym0 _ _ eab) a2 (castf IHA a2) (castf_eq IHA a2)).
        exact (clo_trans _ R _ _ _ ae1 ae2).
      * split. refine (transb IHA C _ eac). apply sym0. exact (castf_eq IHA a2). exact ce.
    + intros a. exists a. exists (castf IHA a). split.
      * eapply clo_refl. eapply refl0.
      * split. exact (castf_eq IHA a). eapply clo_refl. eapply refl0.
    + intros b. exists b. exists (castb IHA b). split.
      * eapply clo_refl. eapply refl0.
      * split. exact (castb_eq IHA b). eapply clo_refl. eapply refl0.
Defined.

Definition trans0@{i j} (A : U0@{i j}) (B : U0@{i j}) (e : eqU0 A B) (C : U0@{i j}) {a b c} :
  eq0 A B a b -> eq0 B C b c -> eq0 A C a c.
Proof.
  exact (fun eab ebc => transf (cast_lemmas A B e) C eab ebc).
Defined.

Definition cast0@{i j} (A : U0@{i j}) (B : U0@{i j}) (e : eqU0 A B) :
  El0 A -> El0 B.
Proof.
  exact (castf (cast_lemmas A B e)).
Defined.

Definition cast0_eq@{i j} (A : U0@{i j}) (B : U0@{i j}) (e : eqU0 A B) :
  forall a, eq0 A B a (cast0 A B e a).
Proof.
  exact (castf_eq (cast_lemmas A B e)).
Defined.

Definition transU0@{i j} {A B C : U0@{i j}} : eqU0 A B -> eqU0 B C -> eqU0 A C.
Proof.
  intro eAB. revert C. change ((fun A B eAB => forall C : U0, eqU0 B C -> eqU0 A C) A B eAB).
  eapply U0_rect2 ; clear eAB B A.
  - intros P Q ePQ. intro C.
    pattern C ; eapply U0_ind ; clear C ; try easy.
    intros R eQR. exact (iff_trans ePQ eQR).
  - easy.
  - easy.
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. intro C.
    pattern C ; eapply U0_ind ; clear C ; try easy.
    intros C _ R _ Re [ eBC eQR ]. unshelve econstructor.
    + exact (IHA C eBC).
    + intros a c eac. set (b := cast0 A B eAB a).
      pose proof (cast0_eq A B eAB a) as eab. change (eq0 A B a b) in eab.
      pose proof (trans0 B A (symU0 A B eAB) C (sym0 A B eab) eac) as ebc.
      exact (IHP a b eab (R c) (eQR b c ebc)).
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. intro C.
    pattern C ; eapply U0_ind ; clear C ; try easy.
    intros C _ R _ Re [ eBC eQR ]. unshelve econstructor.
    + exact (IHA C eBC).
    + intros a c eac. set (b := cast0 A B eAB a).
      pose proof (cast0_eq A B eAB a) as eab. change (eq0 A B a b) in eab.
      pose proof (trans0 B A (symU0 A B eAB) C (sym0 A B eab) eac) as ebc.
      exact (IHP a b eab (R c) (eQR b c ebc)).
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. intro C.
    pattern C ; eapply U0_ind ; clear C ; try easy.
    intros C _ R _ Re [ eBC eQR ]. unshelve econstructor.
    + exact (IHA C eBC).
    + intros a c eac. set (b := cast0 A B eAB a).
      pose proof (cast0_eq A B eAB a) as eab. change (eq0 A B a b) in eab.
      pose proof (trans0 B A (symU0 A B eAB) C (sym0 A B eab) eac) as ebc.
      exact (IHP a b eab (R c) (eQR b c ebc)).
  - intros A B eAB IHA R S eRS Re Se. intro C.
    pattern C ; eapply U0_ind ; clear C ; try easy.
    intros C _ T Te [ eBC eST ]. unshelve econstructor.
    + exact (IHA C eBC).
    + intros a0 c0 eac0 a1 c1 eac1. set (b0 := cast0 A B eAB a0). set (b1 := cast0 A B eAB a1).
      pose proof (cast0_eq A B eAB a0) as eab0. change (eq0 A B a0 b0) in eab0.
      pose proof (trans0 B A (symU0 A B eAB) C (sym0 A B eab0) eac0) as ebc0.
      pose proof (cast0_eq A B eAB a1) as eab1. change (eq0 A B a1 b1) in eab1.
      pose proof (trans0 B A (symU0 A B eAB) C (sym0 A B eab1) eac1) as ebc1.
      exact (iff_trans (eRS a0 b0 eab0 a1 b1 eab1) (eST b0 c0 ebc0 b1 c1 ebc1)).
Defined.

(* Now we define a second universe level which contains U0, the small types, and is closed under Pi.
   One may easily add W, Sigma and Quotients to this new universe, taking inspiration from U0. *)

Inductive inU1@{i j k} : Type@{j} -> Type@{k} :=
| cEmb1 : forall (A : U0@{i j}), inU1 (El0 A)
| cU01 : inU1 U0@{i j}
| cPi1 : forall (A : Type@{j}) (Au : inU1 A) (Aeq : A -> A -> Prop)
                (P : A -> Type@{j}) (Pu : forall (a : A), inU1 (P a))
                (Peq : forall (a0 : A) (a1 : A) (p0 : P a0) (p1 : P a1), Prop),
    inU1 (Sigma (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : Aeq a0 a1), Peq a0 a1 (f a0) (f a1))).

Definition inU1_eq@{i j k} {A : Type@{j}} (Au : inU1@{i j k} A) {B : Type@{j}} (Bu : inU1@{i j k} B) (a : A) (b : B) : Prop.
Proof.
  revert B Bu a b. induction Au as [ A | | A Au IHA Aeq P Pu IHP Peq ].
  - intros _ [ B | | ].
    + exact (fun a b => eq0 A B a b).
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
  - intros _ [ | | ].
    + exact (fun _ _ => False).
    + exact eqU0.
    + exact (fun _ _ => False).
  - intros _ [ | | B Bu Beq Q Qu Qeq ].
    + exact (fun _ _ => False).
    + exact (fun _ _ => False).
    + intros [ f fe ] [ g ge ].
      exact (forall a b, IHA B Bu a b -> IHP a (Q b) (Qu b) (f a) (g b)).
Defined.

Definition inU1_eqU@{i j k} {A : Type@{j}} (Au : inU1@{i j k} A) {B : Type@{j}} (Bu : inU1@{i j k} B) : Prop.
Proof.
  revert B Bu. induction Au as [ A | | A Au IHA Aeq P Pu IHP Peq ].
  - intros _ [ B | | ].
    + exact (eqU0 A B).
    + exact False.
    + exact False.
  - intros _ [ | | ].
    + exact False.
    + exact True.
    + exact False.
  - intros _ [ | | B Bu Beq Q Qu Qeq ].
    + exact False.
    + exact False.
    + exact ((IHA B Bu) /\ (forall a b, inU1_eq Au Bu a b -> IHP a (Q b) (Qu b))).
Defined.

Inductive extU1@{i j k} : forall (A : Type@{j}) (Au : inU1@{i j k} A), Type@{k} :=
| extEmb1 : forall (A : U0), extU1 (El0 A) (cEmb1 A)
| extU01 : extU1 U0 cU01
| extPi1 : forall (A : Type@{j}) (Au : inU1 A) (Ae : extU1 A Au)
                  (P : A -> Type@{j}) (Pu : forall a, inU1 (P a))
                  (Pext : forall a0 a1, inU1_eq Au Au a0 a1 -> inU1_eqU (Pu a0) (Pu a1))
                  (Pe : forall a, extU1 (P a) (Pu a)),
    extU1 (Sigma (forall (a : A), P a) (fun f => forall (a0 a1 : A) (ae : inU1_eq Au Au a0 a1), inU1_eq (Pu a0) (Pu a1) (f a0) (f a1)))
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

Definition eq1 (A B : U1) (a : El1 A) (b : El1 B) : Prop :=
  inU1_eq (in1 A) (in1 B) a b.

Definition eqU1 (A B : U1) : Prop :=
  inU1_eqU (in1 A) (in1 B).

(* Constructors *)

Definition emb1 : U0 -> U1 := fun A => mkU1 (extEmb1 A).
Definition U01 : U1 := mkU1 extU01.
Definition Pi1 (A : U1) (B : El1 A -> U1) (Be : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (B a0) (B a1)) : U1 :=
  mkU1 (extPi1 (El1 A) (in1 A) (ext1 A)
              (fun a => El1 (B a)) (fun a => in1 (B a))
              Be (fun a => ext1 (B a))).

(* Induction principles *)

Definition U1_rect@{i j k l} (X : U1@{i j k} -> Type@{l}) :
  forall (Xemb : forall (A : U0), X (emb1 A))
         (XU : X U01)
         (Xpi : forall (A : U1) (IHA : X A) (P : El1 A -> U1) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1)), X (Pi1 A P Pe))
         (A : U1), X A.
Proof.
  intros.
  destruct A as [A Au Ae]. induction Ae as [ A | | A Au Ae IHA P Pu Pext Pe IHP ].
  - exact (Xemb A).
  - exact XU.
  - exact (Xpi (mkU1 Ae) IHA (fun a => mkU1 (Pe a)) IHP Pext).
Defined.

Definition U1_ind@{i j k} (X : U1@{i j k} -> Prop) :
  forall (Xemb : forall (A : U0), X (emb1 A))
         (XU : X U01)
         (Xpi : forall (A : U1) (IHA : X A) (P : El1 A -> U1) (IHP : forall a, X (P a))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1)), X (Pi1 A P Pe))
         (A : U1), X A.
Proof.
  intros.
  destruct A as [A Au Ae]. induction Ae as [ A | | A Au Ae IHA P Pu Pext Pe IHP ].
  - exact (Xemb A).
  - exact XU.
  - exact (Xpi (mkU1 Ae) IHA (fun a => mkU1 (Pe a)) IHP Pext).
Defined.

Definition U1_rect2@{i j k l} (X : forall (A B : U1@{i j k}), eqU1 A B -> Type@{l}) :
  forall (Xemb : forall (A B : U0@{i j}) (eAB : eqU0 A B), X (emb1 A) (emb1 B) eAB)
         (XU : X U01 U01 I)
         (Xpi : forall (A B : U1@{i j k}) (eAB : eqU1 A B) (IHA : X A B eAB) (P : El1 A -> U1@{i j k}) (Q : El1 B -> U1@{i j k})
                       (ePQ : forall a b, eq1 A B a b -> eqU1 (P a) (Q b))
                       (IHP : forall a b (eab : eq1 A B a b), X (P a) (Q b) (ePQ a b eab))
                       (Pe : forall a0 a1 : El1 A, eq1 A A a0 a1 -> eqU1 (P a0) (P a1))
                       (Qe : forall b0 b1 : El1 B, eq1 B B b0 b1 -> eqU1 (Q b0) (Q b1)),
             X (Pi1 A P Pe) (Pi1 B Q Qe) (conj eAB ePQ))
         (A B : U1@{i j k}) (e : eqU1 A B), X A B e.
Proof.
  intros Xemb XU Xpi A.
  pattern A ; eapply U1_rect@{i j k l} ; clear A.
  - intros A B. pattern B ; eapply U1_rect@{i j k l} ; now intros [].
  - intro B. pattern B ; eapply U1_rect@{i j k l} ; now intros [].
  - intros A IHA P IHP Pe B. pattern B ; eapply U1_rect@{i j k l} ; try (now intros []).
    clear B. intros B _ Q _ Qe [eAB ePQ]. eapply Xpi.
    + exact (IHA B eAB).
    + exact (fun a b eab => IHP a (Q b) (ePQ a b eab)).
Defined.

(* Properties of equalities *)

Definition refl1 (A : U1) (a : El1 A) : eq1 A A a a.
Proof.
  revert a. pattern A ; eapply U1_ind ; clear A.
  - exact refl0.
  - exact reflU0.
  - intros A IHA P IHP Pext [ f fe ]. exact fe.
Defined.

Definition reflU1 (A : U1) : eqU1 A A.
Proof.
  pattern A ; eapply U1_ind ; clear A ; try (now econstructor).
  intro A. exact (reflU0 A).
Defined.

Definition sym1_pre (A B : U1) {a : El1 A} {b : El1 B} : eq1 A B a b <-> eq1 B A b a.
Proof.
  revert B a b. pattern A ; eapply U1_ind ; clear A.
  - intro A. intro B ; pattern B ; eapply U1_ind ; clear B.
    + intros B a b. eapply sym0_pre.
    + intros. split ; now intros [].
    + intros. split ; now intros [].
  - intro B ; pattern B ; eapply U1_ind ; clear B.
    + intros. split ; now intros [].
    + intros A B. eapply symU0_pre.
    + intros. split ; now intros [].
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U1_ind ; clear B.
    + intros a b. split ; now intros [].
    + intros a b. split ; now intros [].
    + intros B _ Q _ Qe f g. split.
      * intros e b a eba. eapply IHP. apply <- IHA in eba. exact (e a b eba).
      * intros e a b eab. eapply IHP. apply IHA in eab. exact (e b a eab).
Defined.

Definition sym1 (A B : U1) {a : El1 A} {b : El1 B} : eq1 A B a b -> eq1 B A b a.
Proof.
  intro e. eapply (sym1_pre A B). exact e.
Defined.

Definition symU1_pre (A B : U1) : eqU1 A B <-> eqU1 B A.
Proof.
  revert B. pattern A ; eapply U1_ind ; clear A.
  - intro A. intro B ; pattern B ; eapply U1_ind ; clear B.
    + intro B. eapply symU0_pre.
    + split ; now intros [].
    + intros. split ; now intros [].
  - intro B ; pattern B ; eapply U1_ind ; clear B.
    + split ; now intros [].
    + easy.
    + intros. split ; now intros [].
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U1_ind ; clear B.
    + split ; now intros [].
    + split ; now intros [].
    + intros B _ Q _ Qe. split.
      * intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
        exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym1. exact eab.
      * intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
        exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym1. exact eab.
Defined.

Definition symU1 (A B : U1) : eqU1 A B -> eqU1 B A.
Proof.
  intro e. eapply (symU1_pre A B). exact e.
Defined.

Set Implicit Arguments.

Record cast_lemmas_conclusion1@{i j k} (A : U1@{i j k}) (B : U1@{i j k}) (e : eqU1 A B) : Type@{j} :=
  {
    transf1 : forall (C : U1@{i j k}) {a b c} (eab : eq1 A B a b) (ebc : eq1 B C b c), eq1 A C a c ;
    transb1 : forall (C : U1@{i j k}) {a b c} (eab : eq1 B A b a) (ebc : eq1 A C a c), eq1 B C b c ;
    castf1 : El1 A -> El1 B ;
    castb1 : El1 B -> El1 A ;
    castf1_eq : forall (a : El1 A), eq1 A B a (castf1 a) ;
    castb1_eq : forall (b : El1 B), eq1 B A b (castb1 b) ;
  }.

Unset Implicit Arguments.

Definition cast_lemmas1@{i j k} (A : U1@{i j k}) (B : U1@{i j k}) (e : eqU1 A B) : cast_lemmas_conclusion1@{i j k} A B e.
Proof.
  eapply U1_rect2 ; clear A B e.
  - intros A B eAB. unshelve econstructor.
    + exact (cast0 A B eAB).
    + exact (castb (cast_lemmas A B eAB)).
    + intro C. pattern C ; eapply U1_ind ; clear C.
      * intros C a b c. eapply (trans0 A B eAB).
      * easy.
      * easy.
    + intro C. pattern C ; eapply U1_ind ; clear C.
      * intros C a b c. eapply (transb (cast_lemmas A B eAB)).
      * easy.
      * easy.
    + intro a. eapply (cast0_eq A B eAB).
    + intro b. eapply (castb_eq (cast_lemmas A B eAB)).
  - unshelve econstructor.
    + exact (fun P => P).
    + exact (fun P => P).
    + intro C. pattern C ; eapply U1_ind ; clear C.
      * easy.
      * intros A B C. eapply transU0.
      * easy.
    + intro C. pattern C ; eapply U1_ind ; clear C.
      * easy.
      * intros A B C. eapply transU0.
      * easy.
    + eapply reflU0.
    + eapply reflU0.
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. unshelve econstructor.
    + intros [ f fe ]. change (forall a0 a1, eq1 A A a0 a1 -> eq1 (P a0) (P a1) (f a0) (f a1)) in fe. unshelve econstructor.
      * refine (fun b => castf1 (IHP _ _ (sym1 B A (castb1_eq IHA b))) (f (castb1 IHA b))).
      * intros b0 b1 eb. change (eq1 B B b0 b1) in eb. cbn.
        pose proof (transf1 IHA B (sym1 B A (castb1_eq IHA b1)) (sym1 B B eb)) as e0.
        pose proof (transf1 IHA A (sym1 B A (castb1_eq IHA b0)) (sym1 A B e0)) as e1.
        pose proof (fe _ _ e1) as e2.
        pose proof (castf1_eq (IHP _ _ (sym1 B A (castb1_eq IHA b1))) (f (castb1 IHA b1))) as e3.
        pose proof (castf1_eq (IHP _ _ (sym1 B A (castb1_eq IHA b0))) (f (castb1 IHA b0))) as e4.
        pose proof (transb1 (IHP _ _ (sym1 B A (castb1_eq IHA b0))) (P (castb1 IHA b1)) (sym1 _ _ e4) e2) as e5.
        exact (transb1 (IHP _ _ e0) (Q b1) e5 e3).
    + intros [ f fe ]. change (forall b0 b1, eq1 B B b0 b1 -> eq1 (Q b0) (Q b1) (f b0) (f b1)) in fe. unshelve econstructor.
      * refine (fun a => castb1 (IHP _ _ (castf1_eq IHA a)) (f (castf1 IHA a))).
      * intros a0 a1 ea. change (eq1 A A a0 a1) in ea. cbn.
        pose proof (transb1 IHA A (sym1 A B (castf1_eq IHA a0)) ea) as e0.
        pose proof (transb1 IHA B e0 (castf1_eq IHA a1)) as e1.
        pose proof (fe _ _ e1) as e2.
        pose proof (castb1_eq (IHP _ _ (castf1_eq IHA a0)) (f (castf1 IHA a0))) as e3.
        pose proof (castb1_eq (IHP _ _ (castf1_eq IHA a1)) (f (castf1 IHA a1))) as e4.
        pose proof (transf1 (IHP _ _ (castf1_eq IHA a1)) (Q (castf1 IHA a0)) (sym1 _ _ e4) (sym1 _ _ e2)) as e5.
        exact (sym1 _ _ (transf1 (IHP _ _ (sym1 B A e0)) (P a0) e5 e3)).
    + intro C. pattern C ; eapply U1_ind ; clear C.
      * easy.
      * easy.
      * intros C _ R _ Re f g h efg egh a c eac. change (eq1 A C a c) in eac.
        set (b := castf1 IHA a).
        pose proof (castf1_eq IHA a) as eab. change (eq1 A B a b) in eab.
        pose proof (transb1 IHA C (sym1 A B eab) eac) as ebc.
        exact (transf1 (IHP a b eab) (R c) (efg _ _ eab) (egh _ _ ebc)).
    + intro C. pattern C ; eapply U1_ind ; clear C.
      * easy.
      * easy.
      * intros C _ R _ Re f g h egf efh b c ebc. change (eq1 B C b c) in ebc.
        set (a := castb1 IHA b).
        pose proof (castb1_eq IHA b) as eba. change (eq1 B A b a) in eba.
        pose proof (transf1 IHA C (sym1 B A eba) ebc) as eac.
        exact (transb1 (IHP a b (sym1 B A eba)) (R c) (egf _ _ eba) (efh _ _ eac)).
    + intros [ f fe ] a b eab. change (eq1 A B a b) in eab.
      pose proof (transf1 IHA A eab (castb1_eq IHA b)) as e0.
      pose proof (fe _ _ e0) as e1. change (eq1 (P a) (P (castb1 IHA b)) (f a) (f (castb1 IHA b))) in e1.
      pose proof (castf1_eq (IHP _ _ (sym1 B A (castb1_eq IHA b))) (f (castb1 IHA b))) as e2.
      exact (sym1 _ _ (transb1 (IHP _ _ (sym1 B A (castb1_eq IHA b))) (P a) (sym1 _ _ e2) (sym1 _ _ e1))).
    + intros [ f fe ] b a eba. change (eq1 B A b a) in eba.
      pose proof (transb1 IHA B eba (castf1_eq IHA a)) as e0.
      pose proof (fe _ _ e0) as e1. change (eq1 (Q b) (Q (castf1 IHA a)) (f b) (f (castf1 IHA a))) in e1.
      pose proof (castb1_eq (IHP _ _ (castf1_eq IHA a)) (f (castf1 IHA a))) as e2.
      exact (sym1 _ _ (transf1 (IHP _ _ (castf1_eq IHA a)) (Q b) (sym1 _ _ e2) (sym1 _ _ e1))).
Defined.

Definition trans1@{i j k} (A : U1@{i j k}) (B : U1@{i j k}) (e : eqU1 A B) (C : U1@{i j k}) {a b c} :
  eq1 A B a b -> eq1 B C b c -> eq1 A C a c.
Proof.
  exact (fun eab ebc => transf1 (cast_lemmas1 A B e) C eab ebc).
Defined.

Definition cast1@{i j k} (A : U1@{i j k}) (B : U1@{i j k}) (e : eqU1 A B) :
  El1 A -> El1 B.
Proof.
  exact (castf1 (cast_lemmas1 A B e)).
Defined.

Definition cast1_eq@{i j k} (A : U1@{i j k}) (B : U1@{i j k}) (e : eqU1 A B) :
  forall a, eq1 A B a (cast1 A B e a).
Proof.
  exact (castf1_eq (cast_lemmas1 A B e)).
Defined.

Definition transU1@{i j k} {A B C : U1@{i j k}} : eqU1 A B -> eqU1 B C -> eqU1 A C.
Proof.
  intro eAB. revert C. change ((fun A B eAB => forall C : U1, eqU1 B C -> eqU1 A C) A B eAB).
  eapply U1_rect2 ; clear eAB B A.
  - intros A B eAB C. pattern C ; eapply U1_ind ; clear C.
    + intros C eBC. apply (transU0 eAB eBC).
    + easy.
    + easy.
  - easy.
  - intros A B eAB IHA P Q ePQ IHP Pe Qe. intro C.
    pattern C ; eapply U1_ind ; clear C.
    + easy.
    + easy.
    + intros C _ R _ Re [ eBC eQR ]. unshelve econstructor.
      * exact (IHA C eBC).
      * intros a c eac. set (b := cast1 A B eAB a).
        pose proof (cast1_eq A B eAB a) as eab. change (eq1 A B a b) in eab.
        pose proof (trans1 B A (symU1 A B eAB) C (sym1 A B eab) eac) as ebc.
        exact (IHP a b eab (R c) (eQR b c ebc)).
Defined.

(* This concludes the construction of our universe of setoids. *)


(* ============================================================================================== *)
(* ============================================================================================== *)
(* ============================================================================================== *)


(* Now we build a model for type theory out of this universe *)

(* A context Gamma is (say) an element of U1, and a dependent type over Gamma is an object of `arr1 Gamma U01`
   In other words, a pair of
   - a map `A : Gamma -> U01`
   - a proof of extensionality `Ae : gamma0 ~ gamma1 -> A gamma0 ~ A gamma1`

   Then given a dependent type A over Gamma, a term of type A is an object of `pi1 Gamma (fun gamma => A gamma) _`
   In other words, a pair of
   - a dependent map `t : forall gamma, A gamma`
   - a proof of extensionality `te : gamma0 ~ gamma1 -> t gamma0 ~ t gamma1`*)

(* U01 is the code for U0 in U1 *)

Check (U01 : U1).
Check (eq_refl : El1 U01 = U0).

(* Non-dependent functions in the higher universe
   Unfortunately, eta-expansion only holds up to a propositional equality *)

Definition arr1 (A B : U1) : U1 := Pi1 A (fun _ => B) (fun _ _ _ => reflU1 B).

Definition arr1e {A0 A1 : U1} (Ae : eqU1 A0 A1) {B0 B1 : U1} (Be : eqU1 B0 B1) : eqU1 (arr1 A0 B0) (arr1 A1 B1).
Proof.
  unshelve econstructor.
  - exact Ae.
  - intros a b eab. exact Be.
Defined.

Definition app1 {A : U1} {B : U1} (f : El1 (arr1 A B)) (a : El1 A) : El1 B.
Proof.
  destruct f as [ f fe ]. exact (f a).
Defined.

Definition app1e {A0 A1 : U1} (Ae : eqU1 A0 A1)
  {B0 B1 : U1} (Be : eqU1 B0 B1)
  {f0 : El1 (arr1 A0 B0)} {f1 : El1 (arr1 A1 B1)} (fe : eq1 (arr1 A0 B0) (arr1 A1 B1) f0 f1)
  {a0 : El1 A0} {a1 : El1 A1} (ae : eq1 A0 A1 a0 a1) : eq1 B0 B1 (app1 f0 a0) (app1 f1 a1).
Proof.
  exact (fe a0 a1 ae).
Defined.

Definition lam1 (A B : U1) (t : El1 A -> El1 B) (te : forall a0 a1 (ae : eq1 A A a0 a1), eq1 B B (t a0) (t a1)) : El1 (arr1 A B).
Proof.
  econstructor. exact te.
Defined.

Definition lam1e {A0 A1 : U1} (Ae : eqU1 A0 A1) {B0 B1 : U1} (Be : eqU1 B0 B1)
  {t0 : El1 A0 -> El1 B0} (t0e : forall a0 a1 (ae : eq1 A0 A0 a0 a1), eq1 B0 B0 (t0 a0) (t0 a1))
  {t1 : El1 A1 -> El1 B1} (t1e : forall a0 a1 (ae : eq1 A1 A1 a0 a1), eq1 B1 B1 (t1 a0) (t1 a1))
  (te : forall a0 a1 (ae : eq1 A0 A1 a0 a1), eq1 B0 B1 (t0 a0) (t1 a1))
  : eq1 (arr1 A0 B0) (arr1 A1 B1) (lam1 A0 B0 t0 t0e) (lam1 A1 B1 t1 t1e).
Proof.
  exact te.
Defined.

(* Dependent functions in the lower universe
   Unfortunately, eta-expansion only holds up to a propositional equality *)

Definition pi0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01)) : El1 U01.
Proof.
  destruct P as [ P Pe ].
  exact (Pi0 A P Pe).
Defined.

Definition pi0e {A B : El1 U01} (eAB : eq1 U01 U01 A B)
  {P : El1 (arr1 (emb1 A) U01)} {Q : El1 (arr1 (emb1 B) U01)} (ePQ : eq1 (arr1 (emb1 A) U01) (arr1 (emb1 B) U01) P Q)
  : eq1 U01 U01 (pi0 A P) (pi0 B Q).
Proof.
  destruct P as [ P Pe ]. destruct Q as [ Q Qe ].
  unshelve econstructor.
  - exact eAB.
  - intros a b eab. exact (ePQ a b eab).
Defined.

Definition arr0 (A B : El1 U01) : El1 U01 := pi0 A (lam1 (emb1 A) U01 (fun _ => B) (fun _ _ _ => reflU0 B)).

Definition arr0e {A0 A1 : U0} (Ae : eqU0 A0 A1) {B0 B1 : U0} (Be : eqU0 B0 B1) : eqU0 (arr0 A0 B0) (arr0 A1 B1).
Proof.
  refine (@pi0e _ _ Ae (lam1 (emb1 A0) U01 (fun _ => B0) (fun _ _ _ => reflU0 B0)) (lam1 (emb1 A1) U01 (fun _ => B1) (fun _ _ _ => reflU0 B1)) (fun _ _ _ => Be)).
Defined.

Definition app0 {A : El1 U01} {P : El1 (arr1 (emb1 A) U01)} (f : El0 (pi0 A P)) (a : El0 A) : El0 (app1 P a).
Proof.
  destruct f as [ f fe ].
  exact (f a).
Defined.

Definition app0e {A B : El1 U01} (eAB : eq1 U01 U01 A B)
  {P : El1 (arr1 (emb1 A) U01)} {Q : El1 (arr1 (emb1 B) U01)} (ePQ : eq1 (arr1 (emb1 A) U01) (arr1 (emb1 B) U01) P Q)
  {f : El0 (pi0 A P)} {g : El0 (pi0 B Q)} (efg : eq0 (pi0 A P) (pi0 B Q) f g)
  {a : El0 A} {b : El0 B} (eab : eq0 A B a b)
  : eq0 (app1 P a) (app1 Q b) (app0 f a) (app0 g b).
Proof.
  exact (efg a b eab).
Defined.

Definition lam0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01))
  (t : forall a : El0 A, El0 (app1 P a)) (te : forall a0 a1 (ae : eq0 A A a0 a1), eq0 (app1 P a0) (app1 P a1) (t a0) (t a1))
  : El0 (pi0 A P).
Proof.
  exact {| fst := t; snd := te |}.
Defined.

Definition lam0e {A0 A1 : El1 U01} (Ae : eqU0 A0 A1)
  {P0 : El1 (arr1 (emb1 A0) U01)} {P1 : El1 (arr1 (emb1 A1) U01)} (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  {t0 : forall a : El0 A0, El0 (app1 P0 a)} (t0e : forall a0 a1 (ae : eq0 A0 A0 a0 a1), eq0 (app1 P0 a0) (app1 P0 a1) (t0 a0) (t0 a1))
  {t1 : forall a : El0 A1, El0 (app1 P1 a)} (t1e : forall a0 a1 (ae : eq0 A1 A1 a0 a1), eq0 (app1 P1 a0) (app1 P1 a1) (t1 a0) (t1 a1))
  (te : forall a0 a1 (ae : eq0 A0 A1 a0 a1), eq0 (app1 P0 a0) (app1 P1 a1) (t0 a0) (t1 a1))
  : eq0 (pi0 A0 P0) (pi0 A1 P1) (lam0 A0 P0 t0 t0e) (lam0 A1 P1 t1 t1e).
Proof.
  exact te.
Defined.

Definition beta0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01))
  (t : forall a : El0 A, El0 (app1 P a)) (te : forall a0 a1 (ae : eq0 A A a0 a1), eq0 (app1 P a0) (app1 P a1) (t a0) (t a1))
  (a : El0 A) : app0 (lam0 A P t te) a = t a.
Proof.
  reflexivity.
Defined.

Definition beta0e {A0 A1 : El1 U01} (Ae : eqU0 A0 A1)
  {P0 : El1 (arr1 (emb1 A0) U01)} {P1 : El1 (arr1 (emb1 A1) U01)} (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  {t0 : forall a : El0 A0, El0 (app1 P0 a)} (t0e : forall a0 a1 (ae : eq0 A0 A0 a0 a1), eq0 (app1 P0 a0) (app1 P0 a1) (t0 a0) (t0 a1))
  {t1 : forall a : El0 A1, El0 (app1 P1 a)} (t1e : forall a0 a1 (ae : eq0 A1 A1 a0 a1), eq0 (app1 P1 a0) (app1 P1 a1) (t1 a0) (t1 a1))
  (te : forall a0 a1 (ae : eq0 A0 A1 a0 a1), eq0 (app1 P0 a0) (app1 P1 a1) (t0 a0) (t1 a1))
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1) : app0e Ae Pe (lam0e Ae Pe t0e t1e te) ae = te _ _ ae.
Proof.
  reflexivity.
Defined.

(* Sigma types *)

Definition sigma0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01)) : El1 U01.
Proof.
  destruct P as [ P Pe ].
  exact (Sigma0 A P Pe).
Defined.

Definition sigma0e {A B : El1 U01} (eAB : eq1 U01 U01 A B)
  {P : El1 (arr1 (emb1 A) U01)} {Q : El1 (arr1 (emb1 B) U01)} (ePQ : eq1 (arr1 (emb1 A) U01) (arr1 (emb1 B) U01) P Q)
  : eq1 U01 U01 (sigma0 A P) (sigma0 B Q).
Proof.
  destruct P as [ P Pe ]. destruct Q as [ Q Qe ].
  unshelve econstructor.
  - exact eAB.
  - intros a b eab. exact (ePQ a b eab).
Defined.

Definition pair0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01))
  (a : El0 A) (p : El0 (app1 P a)) : El0 (sigma0 A P).
Proof.
  econstructor. exact p.
Defined.

Definition pair0e {A0 A1 : El1 U01} (Ae : eq1 U01 U01 A0 A1)
  {P0 : El1 (arr1 (emb1 A0) U01)} {P1 : El1 (arr1 (emb1 A1) U01)} (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  {a0 : El0 A0} {a1 : El0 A1} (ae : eq0 A0 A1 a0 a1)
  (p0 : El0 (app1 P0 a0)) (p1 : El0 (app1 P1 a1)) (pe : eq0 (app1 P0 a0) (app1 P1 a1) p0 p1)
  : eq0 (sigma0 A0 P0) (sigma0 A1 P1) (pair0 A0 P0 a0 p0) (pair0 A1 P1 a1 p1).
Proof.
  econstructor.
  - exact ae.
  - exact pe.
Defined.

Definition fst0 {A : El1 U01} {P : El1 (arr1 (emb1 A) U01)}
  (t : El0 (sigma0 A P)) : El0 A.
Proof.
  exact (fst t).
Defined.

Definition fst0e {A0 A1 : El1 U01} (Ae : eqU0 A0 A1)
  {P0 : El1 (arr1 (emb1 A0) U01)} {P1 : El1 (arr1 (emb1 A1) U01)} (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  {t0 : El0 (sigma0 A0 P0)} {t1 : El0 (sigma0 A1 P1)} {te : eq0 (sigma0 A0 P0) (sigma0 A1 P1) t0 t1}
  : eq0 A0 A1 (fst0 t0) (fst0 t1).
Proof.
  exact (andleft te).
Defined.

Definition snd0 {A : El1 U01} {P : El1 (arr1 (emb1 A) U01)}
  (t : El0 (sigma0 A P)) : El0 (fst P (fst0 t)).
Proof.
  exact (snd t).
Defined.

Definition snd0e {A0 A1 : El1 U01} (Ae : eqU0 A0 A1)
  {P0 : El1 (arr1 (emb1 A0) U01)} {P1 : El1 (arr1 (emb1 A1) U01)} (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  {t0 : El0 (sigma0 A0 P0)} {t1 : El0 (sigma0 A1 P1)} {te : eq0 (sigma0 A0 P0) (sigma0 A1 P1) t0 t1}
  : eq0 (fst P0 (fst0 t0)) (fst P1 (fst0 t1)) (snd0 t0) (snd0 t1).
Proof.
  exact (andright te).
Defined.

(* impredicative quantification *)

Definition forall0 (A : El1 U01) (P : El0 (arr0 A Prop0)) : El0 Prop0.
Proof.
  destruct P as [ P Pe ].
  exact (forall (a : El0 A), P a).
Defined.

Definition forall0e {A B : El1 U01} (eAB : eq1 U01 U01 A B)
  {P : El0 (arr0 A Prop0)} {Q : El0 (arr0 B Prop0)} (ePQ : eq0 (arr0 A Prop0) (arr0 B Prop0) P Q)
  : eq0 Prop0 Prop0 (forall0 A P) (forall0 B Q).
Proof.
  destruct P as [ P Pe ]. destruct Q as [ Q Qe ].
  unshelve econstructor.
  - intros f b. set (a := cast0 B A (symU0 A B eAB) b).
    pose proof (cast0_eq B A (symU0 A B eAB) b) as eab. change (eq0 B A b a) in eab.
    pose proof (ePQ a b (sym0 B A eab)) as e0. change ((P a) <-> (Q b)) in e0.
    destruct e0 as [ H _ ]. exact (H (f a)).
  - intros f a. set (b := cast0 A B eAB a).
    pose proof (cast0_eq A B eAB a) as eab. change (eq0 A B a b) in eab.
    pose proof (ePQ a b eab) as e0. change ((P a) <-> (Q b)) in e0.
    destruct e0 as [ _ H ]. exact (H (f b)).
Defined.

Definition forall_app0 {A : El1 U01} {P : El0 (arr0 A Prop0)} (f : (forall0 A P)) (a : El0 A) : (fst P a).
Proof.
  exact (f a).
Defined.

Definition forall_lam0 (A : El1 U01) (P : El0 (arr0 A Prop0))
  (t : forall a : El0 A, fst P a) : forall0 A P.
Proof.
  exact t.
Defined.

(* Natural numbers *)

Check (nat0 : U0).

Definition zero0 : El0 nat0 := zero.

Definition suc0 (n : El0 nat0) : El0 nat0 := suc n.

Definition suc0e {n m : El0 nat0} (enm : eq0 nat0 nat0 n m) : eq0 nat0 nat0 (suc0 n) (suc0 m) := eqsuc n m enm.

Definition natrec0 (P : El1 (arr1 (emb1 nat0) U01)) (Pz : El0 (app1 P zero0))
  (Ps : El0 (pi0 nat0
               (lam1 (emb1 nat0) U01
                  (fun n => arr0 (app1 P n) (app1 P (suc0 n)))
                  (fun n m e => arr0e (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P) e) (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P) (suc0e e))))))
  (n : El0 nat0) : El0 (app1 P n).
Proof.
  refine (nat_rect (fun n => El0 (app1 P n)) Pz (fun m Pn => fst ((fst Ps) m) Pn) n).
Defined.

Definition natrec0e
  {P0 : El1 (arr1 (emb1 nat0) U01)} {P1 : El1 (arr1 (emb1 nat0) U01)} (Pe : eq1 (arr1 (emb1 nat0) U01) (arr1 (emb1 nat0) U01) P0 P1)
  {P0z : El0 (app1 P0 zero0)} {P1z : El0 (app1 P1 zero0)} (Pez : eq0 (app1 P0 zero0) (app1 P1 zero0) P0z P1z)
  {P0s : El0 (pi0 nat0
               (lam1 (emb1 nat0) U01
                  (fun n => arr0 (app1 P0 n) (app1 P0 (suc0 n)))
                  (fun n m e => arr0e (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P0) e) (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P0) (suc0e e)))))}
  {P1s : El0 (pi0 nat0
               (lam1 (emb1 nat0) U01
                  (fun n => arr0 (app1 P1 n) (app1 P1 (suc0 n)))
                  (fun n m e => arr0e (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P1) e) (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P1) (suc0e e)))))}
  (Pes : eq0
           (pi0 nat0 (lam1 (emb1 nat0) U01 (fun n => arr0 (app1 P0 n) (app1 P0 (suc0 n))) (fun n m e => arr0e (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P0) e) (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P0) (suc0e e)))))
           (pi0 nat0 (lam1 (emb1 nat0) U01 (fun n => arr0 (app1 P1 n) (app1 P1 (suc0 n))) (fun n m e => arr0e (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P1) e) (app1e (reflU1 (emb1 nat0)) (reflU1 U01) (refl1 _ P1) (suc0e e)))))
           P0s P1s)
  (n0 n1 : El0 nat0) (ne : eq0 nat0 nat0 n0 n1)
  : eq0 (app1 P0 n0) (app1 P1 n1) (natrec0 P0 P0z P0s n0) (natrec0 P1 P1z P1s n1).
Proof.
  induction ne.
  - exact Pez.
  - exact (Pes n m ne _ _ IHne).
Defined.

(* W types *)

Definition Wtype0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01)) : El1 U01.
Proof.
  destruct P as [ P Pe ].
  exact (W0 A P Pe).
Defined.

Definition Wtype0e {A B : El1 U01} (eAB : eq1 U01 U01 A B)
  {P : El1 (arr1 (emb1 A) U01)} {Q : El1 (arr1 (emb1 B) U01)} (ePQ : eq1 (arr1 (emb1 A) U01) (arr1 (emb1 B) U01) P Q)
  : eq1 U01 U01 (Wtype0 A P) (Wtype0 B Q).
Proof.
  destruct P as [ P Pe ]. destruct Q as [ Q Qe ].
  unshelve econstructor.
  - exact eAB.
  - intros a b eab. exact (ePQ a b eab).
Defined.

Definition sup0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01))
  (a : El0 A) (f : El0 (arr0 (app1 P a) (Wtype0 A P))) : El0 (Wtype0 A P).
Proof.
  unshelve econstructor.
  - exact (sup a (fun p => fst (fst f p))).
  - exact (extsup a (fun p => fst (fst f p)) (fun p => snd (fst f p)) (snd f)).
Defined.

Definition sup0e (A0 A1 : El1 U01) (Ae : eqU0 A0 A1)
  (P0 : El1 (arr1 (emb1 A0) U01)) (P1 : El1 (arr1 (emb1 A1) U01)) (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (f0 : El0 (arr0 (app1 P0 a0) (Wtype0 A0 P0))) (f1 : El0 (arr0 (app1 P1 a1) (Wtype0 A1 P1)))
  (fe : eq0 (arr0 (app1 P0 a0) (Wtype0 A0 P0)) (arr0 (app1 P1 a1) (Wtype0 A1 P1)) f0 f1)
  : eq0 (Wtype0 A0 P0) (Wtype0 A1 P1) (sup0 A0 P0 a0 f0) (sup0 A1 P1 a1 f1).
Proof.
  constructor.
  - exact ae.
  - intros p0 p1 pe. exact (fe p0 p1 pe).
Defined.

Definition welim0_IH (A : El1 U01) (P : El1 (arr1 (emb1 A) U01)) (X : El1 (arr1 (emb1 (Wtype0 A P)) U01)) : U0.
Proof.
  unshelve refine (Pi0 A (fun a => Pi0 (arr0 (app1 P a) (Wtype0 A P))
                            (fun f => arr0 (Pi0 (app1 P a) (fun p => app1 X (fst f p)) _) (app1 X (sup0 A P a f))) _) _).
  - intros p0 p1 pe. exact (snd X (fst f p0) (fst f p1) (snd f p0 p1 pe)).
  - intros f0 f1 fe. eapply arr0e.
    + constructor.
      * apply reflU0.
      * intros p0 p1 pe. exact (snd X (fst f0 p0) (fst f1 p1) (fe p0 p1 pe)).
    + refine (snd X (sup0 A P a f0) (sup0 A P a f1) _). constructor.
      * apply refl0.
      * intros p0 p1 pe. exact (fe p0 p1 pe).
  - intros a0 a1 ae. constructor.
    + eapply arr0e.
      * exact (snd P a0 a1 ae).
      * apply reflU0.
    + intros f0 f1 fe. eapply arr0e.
      * constructor.
        ** exact (snd P a0 a1 ae).
        ** intros p0 p1 pe. exact (snd X _ _ (fe p0 p1 pe)).
      * refine (snd X (sup0 A P a0 f0) (sup0 A P a1 f1) _). constructor.
        ** exact ae.
        ** intros p0 p1 pe. exact (fe p0 p1 pe).
Defined.

Inductive inWRect (A : U0) (P : El1 (arr1 (emb1 A) U01)) (X : El1 (arr1 (emb1 (Wtype0 A P)) U01)) (IH : El0 (welim0_IH A P X))
  : forall (w : El0 (Wtype0 A P)) (x : El0 (fst X w)), Type :=
| inRectsup : forall (a : El0 A) (f : El0 (arr0 (app1 P a) (Wtype0 A P)))
                     (rec : El0 (Pi0 (app1 P a) (fun p => fst X (fst f p)) (fun p0 p1 pe => snd X _ _ (snd f p0 p1 pe))))
                     (Hrec : forall (p : El0 (app1 P a)), inWRect A P X IH (fst f p) (fst rec p))
  , inWRect A P X IH (sup0 A P a f) (fst (fst (fst IH a) f) rec).

Definition inWRect_eq (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (P0 : El1 (arr1 (emb1 A0) U01)) (P1 : El1 (arr1 (emb1 A1) U01)) (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  (X0 : El1 (arr1 (emb1 (Wtype0 A0 P0)) U01)) (X1 : El1 (arr1 (emb1 (Wtype0 A1 P1)) U01))
  (Xe : eq1 (arr1 (emb1 (Wtype0 A0 P0)) U01) (arr1 (emb1 (Wtype0 A1 P1)) U01) X0 X1)
  (IH0 : El0 (welim0_IH A0 P0 X0)) (IH1 : El0 (welim0_IH A1 P1 X1)) (IHe : eq0 (welim0_IH A0 P0 X0) (welim0_IH A1 P1 X1) IH0 IH1)
  : forall (w0 : El0 (Wtype0 A0 P0)) (w1 : El0 (Wtype0 A1 P1)) (we : eq0 (Wtype0 A0 P0) (Wtype0 A1 P1) w0 w1)
           (x0 : El0 (fst X0 w0)) (x1 : El0 (fst X1 w1))
           (Hx0 : inWRect A0 P0 X0 IH0 w0 x0) (Hx1 : inWRect A1 P1 X1 IH1 w1 x1)
  , eq0 (fst X0 w0) (fst X1 w1) x0 x1.
Proof.
  intros w0 w1 we x0 x1 Hx0. revert w1 we x1. induction Hx0 as [ a0 f0 rec0 Hrec0 IHx0 ].
  intros w1 we x1 Hx1. destruct Hx1 as [ a1 f1 rec1 Hrec1 ].
  change (Weq (eq0 A0 A1) (fun a0 a1 => eq0 (fst P0 a0) (fst P1 a1)) (fst (sup0 A0 P0 a0 f0)) (fst (sup0 A1 P1 a1 f1))) in we.
  apply Weq_inversion in we. destruct we as [ ae fe ].
  refine (IHe a0 a1 ae f0 f1 fe rec0 rec1 _).
  change (forall p0 p1 (pe : eq0 (app1 P0 a0) (app1 P1 a1) p0 p1)
           , (eq0 (app1 X0 (fst f0 p0)) (app1 X1 (fst f1 p1)) (fst rec0 p0) (fst rec1 p1))).
  intros p0 p1 pe.
  refine (IHx0 p0 (fst f1 p1) (fe p0 p1 pe) (fst rec1 p1) (Hrec1 p1)).
Defined.

Definition WRect (A : El1 U01) (P : El1 (arr1 (emb1 A) U01)) (X : El1 (arr1 (emb1 (Wtype0 A P)) U01))
  (IH : El0 (welim0_IH A P X)) (w : El0 (Wtype0 A P))
  : Sigma (El0 (app1 X w)) (inWRect A P X IH w).
Proof.
  destruct w as [ w we ].
  induction we as [ a f fe IHf fext ].
  unshelve epose (f0 := _ : El0 (arr0 (app1 P a) (Wtype0 A P))).
  { unshelve econstructor.
    - exact (fun p => {| fst := f p ; snd := fe p |}).
    - exact fext. }
  unshelve epose (rec := _ : El0 (Pi0 (app1 P a) (fun p => fst X (fst f0 p)) (fun p0 p1 pe => snd X _ _ (snd f0 p0 p1 pe)))).
  { unshelve econstructor.
    - intro p. exact (fst (IHf p)).
    - intros p0 p1 pe. refine (inWRect_eq A A (reflU0 A) P P (refl1 (arr1 (emb1 A) U01) P)
                                 X X (refl1 (arr1 (emb1 (Wtype0 A P)) U01) X) IH IH (refl0 (welim0_IH A P X) IH)
                                 (fst f0 p0) (fst f0 p1) (snd f0 p0 p1 pe) _ _ _ _).
      + exact (snd (IHf p0)).
      + exact (snd (IHf p1)). }
  unshelve epose (Hrec := _ : forall (p : El0 (app1 P a)), inWRect A P X IH (fst f0 p) (fst rec p)).
  { intro p. exact (snd (IHf p)). }
  econstructor.
  exact (inRectsup A P X IH a f0 rec Hrec).
Defined.

Definition welim0 (A : El1 U01) (P : El1 (arr1 (emb1 A) U01)) (X : El1 (arr1 (emb1 (Wtype0 A P)) U01))
  (IH : El0 (welim0_IH A P X))
  (w : El0 (Wtype0 A P)) : El0 (app1 X w).
Proof.
  exact (fst (WRect A P X IH w)).
Defined.

Definition welim0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (P0 : El1 (arr1 (emb1 A0) U01)) (P1 : El1 (arr1 (emb1 A1) U01)) (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  (X0 : El1 (arr1 (emb1 (Wtype0 A0 P0)) U01)) (X1 : El1 (arr1 (emb1 (Wtype0 A1 P1)) U01))
  (Xe : eq1 (arr1 (emb1 (Wtype0 A0 P0)) U01) (arr1 (emb1 (Wtype0 A1 P1)) U01) X0 X1)
  (IH0 : El0 (welim0_IH A0 P0 X0)) (IH1 : El0 (welim0_IH A1 P1 X1)) (IHe : eq0 (welim0_IH A0 P0 X0) (welim0_IH A1 P1 X1) IH0 IH1)
  (w0 : El0 (Wtype0 A0 P0)) (w1 : El0 (Wtype0 A1 P1)) (we : eq0 (Wtype0 A0 P0) (Wtype0 A1 P1) w0 w1)
  : eq0 (app1 X0 w0) (app1 X1 w1) (welim0 A0 P0 X0 IH0 w0) (welim0 A1 P1 X1 IH1 w1).
Proof.
  exact (inWRect_eq A0 A1 Ae P0 P1 Pe X0 X1 Xe IH0 IH1 IHe w0 w1 we
           (fst (WRect A0 P0 X0 IH0 w0)) (fst (WRect A1 P1 X1 IH1 w1))
           (snd (WRect A0 P0 X0 IH0 w0)) (snd (WRect A1 P1 X1 IH1 w1))).
Defined.

(* equality *)

Definition id0 (A : U0) (a b : El0 A) : El0 Prop0.
Proof.
  exact (eq0 A A a b).
Defined.

Definition id0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (b0 : El0 A0) (b1 : El0 A1) (be : eq0 A0 A1 b0 b1)
  : eq0 Prop0 Prop0 (id0 A0 a0 b0) (id0 A1 a1 b1).
Proof.
  split.
  - intro e0. pose proof (trans0 A1 A0 (symU0 A0 A1 Ae) A0 (sym0 A0 A1 ae) e0) as e1.
    exact (trans0 A1 A0 (symU0 A0 A1 Ae) A1 e1 be).
  - intro e0. pose proof (trans0 A0 A1 Ae A1 ae e0) as e1.
    exact (trans0 A0 A1 Ae A0 e1 (sym0 A0 A1 be)).
Defined.

Definition idrefl0 (A : U0) (a : El0 A) : id0 A a a.
Proof.
  exact (refl0 A a).
Defined.

Definition id1 (A : U1) (a b : El1 A) : El0 Prop0.
Proof.
  exact (eq1 A A a b).
Defined.

Definition id1e (A0 A1 : U1) (Ae : eqU1 A0 A1)
  (a0 : El1 A0) (a1 : El1 A1) (ae : eq1 A0 A1 a0 a1)
  (b0 : El1 A0) (b1 : El1 A1) (be : eq1 A0 A1 b0 b1)
  : eq0 Prop0 Prop0 (id1 A0 a0 b0) (id1 A1 a1 b1).
Proof.
  split.
  - intro e0. pose proof (trans1 A1 A0 (symU1 A0 A1 Ae) A0 (sym1 A0 A1 ae) e0) as e1.
    exact (trans1 A1 A0 (symU1 A0 A1 Ae) A1 e1 be).
  - intro e0. pose proof (trans1 A0 A1 Ae A1 ae e0) as e1.
    exact (trans1 A0 A1 Ae A0 e1 (sym1 A0 A1 be)).
Defined.

Definition idrefl1 (A : U1) (a : El1 A) : id1 A a a.
Proof.
  exact (refl1 A a).
Defined.

Definition idcast0 (A B : U0) (e : id1 U01 A B) (a : El0 A) : El0 B.
Proof.
  exact (cast0 A B e a).
Defined.

Definition idcast0e (A0 A1 : U0) (Ae : eqU0 A0 A1) (B0 B1 : U0) (Be : eqU0 B0 B1)
  (e0 : id1 U01 A0 B0) (e1 : id1 U01 A1 B1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1) : eq0 B0 B1 (idcast0 A0 B0 e0 a0) (idcast0 A1 B1 e1 a1).
Proof.
  pose proof (sym0 A0 B0 (cast0_eq A0 B0 e0 a0)) as h0.
  pose proof (trans0 B0 A0 (symU0 A0 B0 e0) A1 h0 ae) as h1.
  refine (trans0 B0 A1 _ B1 h1 (cast0_eq A1 B1 e1 a1)).
  exact (transU0 Be (symU0 A1 B1 e1)).
Defined.

(* then we can show symmetry, transitivity, fapply, funext, propext... *)

(* Accessibility predicate *)

Definition Acc0 (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (a : El0 A) : El0 Prop0.
Proof.
  exact (Acc (El0 A) (fun a b => fst (fst R a) b) a).
Defined.

Definition Acc0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 Prop0))) (R1 : El0 (arr0 A1 (arr0 A1 Prop0)))
  (Re : eq0 (arr0 A0 (arr0 A0 Prop0)) (arr0 A1 (arr0 A1 Prop0)) R0 R1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1) : eq0 Prop0 Prop0 (Acc0 A0 R0 a0) (Acc0 A1 R1 a1).
Proof.
  split.
  - intro Hacc. revert a1 ae. induction Hacc as [ a0 Ha0 IH ].
    intros a1 ae. refine (acc _ _ a1 (fun b1 Hb1 => _)). simpl in Hb1.
    set (b0 := cast0 A1 A0 (symU0 A0 A1 Ae) b1).
    pose proof (sym0 A1 A0 (cast0_eq A1 A0 (symU0 A0 A1 Ae) b1)) as be. change (eq0 A0 A1 b0 b1) in be.
    assert (fst (fst R0 b0) a0) as Hb0.
    { apply (Re b0 b1 be a0 a1 ae). exact Hb1. }
    exact (IH b0 Hb0 b1 be).
  - intro Hacc. revert a0 ae. induction Hacc as [ a1 Ha1 IH ].
    intros a0 ae. refine (acc _ _ a0 (fun b0 Hb0 => _)). simpl in Hb0.
    set (b1 := cast0 A0 A1 Ae b0).
    pose proof (cast0_eq A0 A1 Ae b0) as be. change (eq0 A0 A1 b0 b1) in be.
    assert (fst (fst R1 b1) a1) as Hb1.
    { apply (Re b0 b1 be a0 a1 ae). exact Hb0. }
    exact (IH b1 Hb1 b0 be).
Defined.

Definition acc0 (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (a : El0 A)
  (Ha : forall (b : El0 A), fst (fst R b) a -> Acc0 A R b)
  : Acc0 A R a.
Proof.
  exact (acc (El0 A) (fun a b => fst (fst R a) b) a Ha).
Defined.

Definition accelim0_IH (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (X : El1 (arr1 (emb1 A) U01)) : U0.
Proof.
  unshelve refine (Pi0 A (fun a => (arr0 (emb0 (forall b : El0 A, (fst (fst R b) a) -> Acc0 A R b))
                                      (arr0 (Pi0 A (fun b => arr0 (emb0 (fst (fst R b) a)) (app1 X b)) _)
                                         (app1 X a)))) _).
  - intros b0 b1 be. refine (arr0e _ _).
    + exact (snd R b0 b1 be a a (refl0 A a)).
    + exact (snd X b0 b1 be).
  - intros a0 a1 ae. refine (arr0e _ _).
    + split.
      * intros H b Ha1. apply H. apply (snd R b b (refl0 A b) a0 a1 ae). exact Ha1.
      * intros H b Ha0. apply H. apply (snd R b b (refl0 A b) a0 a1 ae). exact Ha0.
    + refine (arr0e _ _).
      * econstructor. exact (reflU0 A).
        intros b0 b1 be. change (eqU0 (arr0 (emb0 (fst (fst R b0) a0)) (app1 X b0)) (arr0 (emb0 (fst (fst R b1) a1)) (app1 X b1))).
        refine (arr0e _ _).
        ** exact (snd R b0 b1 be a0 a1 ae).
        ** exact (snd X b0 b1 be).
      * exact (snd X a0 a1 ae).
Defined.

Inductive inAccRect (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (X : El1 (arr1 (emb1 A) U01)) (IH : El0 (accelim0_IH A R X))
  : forall (a : El0 A) (h : Acc0 A R a) (x : El0 (fst X a)), Type :=
| inRectacc : forall (a : El0 A) (Ha : forall (b : El0 A), fst (fst R b) a -> Acc0 A R b)
                     (rec : El0 (Pi0 A (fun b => arr0 (emb0 (fst (fst R b) a)) (app1 X b))
                                   (fun (b0 b1 : El0 A) (be : eq0 A A b0 b1) =>
                                      @arr0e (emb0 (fst (fst R b0) a)) (emb0 (fst (fst R b1) a)) (snd R b0 b1 be a a (refl0 A a))
                                        (fst X b0) (fst X b1) (snd X b0 b1 be))))
                     (Hrec : forall (b : El0 A) (Hb : fst (fst R b) a), inAccRect A R X IH b (Ha b Hb) (fst (fst rec b) Hb))
  , inAccRect A R X IH a (acc0 A R a Ha) (fst (fst (fst IH a) Ha) rec).

Definition inAccRect_eq (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 Prop0))) (R1 : El0 (arr0 A1 (arr0 A1 Prop0))) (Re : eq0 (arr0 A0 (arr0 A0 Prop0)) (arr0 A1 (arr0 A1 Prop0)) R0 R1)
  (X0 : El1 (arr1 (emb1 A0) U01)) (X1 : El1 (arr1 (emb1 A1) U01)) (Xe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) X0 X1)
  (IH0 : El0 (accelim0_IH A0 R0 X0)) (IH1 : El0 (accelim0_IH A1 R1 X1)) (IHe : eq0 (accelim0_IH A0 R0 X0) (accelim0_IH A1 R1 X1) IH0 IH1)
  : forall (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
           (h0 : Acc0 A0 R0 a0) (h1 : Acc0 A1 R1 a1)
           (x0 : El0 (fst X0 a0)) (x1 : El0 (fst X1 a1))
           (Hx0 : inAccRect A0 R0 X0 IH0 a0 h0 x0) (Hx1 : inAccRect A1 R1 X1 IH1 a1 h1 x1)
  , eq0 (fst X0 a0) (fst X1 a1) x0 x1.
Proof.
  intros a0 a1 ae h0 h1 x0 x1 Hx0. revert a1 ae h1 x1. induction Hx0 as [ a0 Ha0 rec0 Hrec0 IHx0 ].
  intros a1 ae h1 x1 Hx1. destruct Hx1 as [ a1 Ha1 rec1 Hrec1 ].
  refine (IHe a0 a1 ae Ha0 Ha1 I rec0 rec1 _).
  change (forall b0 b1 (be : eq0 A0 A1 b0 b1) (Hb0 : (fst (fst R0 b0) a0)) (Hb1 : (fst (fst R1 b1) a1)) (Hbe : True)
           , eq0 (app1 X0 b0) (app1 X1 b1) (fst (fst rec0 b0) Hb0) (fst (fst rec1 b1) Hb1)).
  intros b0 b1 be Hb0 Hb1 _.
  refine (IHx0 b0 Hb0 b1 be (Ha1 b1 Hb1) (fst (fst rec1 b1) Hb1) (Hrec1 b1 Hb1)).
Defined.

Definition AccRect (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (X : El1 (arr1 (emb1 A) U01)) (IH : El0 (accelim0_IH A R X))
  (a : El0 A) (h : Acc0 A R a) : Sigma (El0 (app1 X a)) (inAccRect A R X IH a h).
Proof.
  revert a h. eapply Acc_rect_ex. intros a Ha IHa.
  unshelve epose (rec := _ : El0 (Pi0 A (fun b => arr0 (emb0 (fst (fst R b) a)) (app1 X b))
                                   (fun (b0 b1 : El0 A) (be : eq0 A A b0 b1) =>
                                      @arr0e (emb0 (fst (fst R b0) a)) (emb0 (fst (fst R b1) a)) (snd R b0 b1 be a a (refl0 A a))
                                        (fst X b0) (fst X b1) (snd X b0 b1 be)))).
  { unshelve econstructor.
    - intro b. unshelve econstructor.
      + intro Hb. exact (fst (IHa b Hb)).
      + intros Hb0 Hb1 _. simpl.
        exact (inAccRect_eq A A (reflU0 A) R R (refl0 (arr0 A (arr0 A Prop0)) R)
                 X X (refl1 (arr1 (emb1 A) U01) X) IH IH (refl0 (accelim0_IH A R X) IH)
                 b b (refl0 A b) (Ha b Hb0) (Ha b Hb1) (fst (IHa b Hb0)) (fst (IHa b Hb1)) (snd (IHa b Hb0)) (snd (IHa b Hb1))).
    - intros b0 b1 be Hb0 Hb1 _. simpl.
      exact (inAccRect_eq A A (reflU0 A) R R (refl0 (arr0 A (arr0 A Prop0)) R)
               X X (refl1 (arr1 (emb1 A) U01) X) IH IH (refl0 (accelim0_IH A R X) IH)
               b0 b1 be (Ha b0 Hb0) (Ha b1 Hb1) (fst (IHa b0 Hb0)) (fst (IHa b1 Hb1)) (snd (IHa b0 Hb0)) (snd (IHa b1 Hb1))). }
  unshelve epose (Hrec := _ : forall (b : El0 A) (Hb : fst (fst R b) a), inAccRect A R X IH b (Ha b Hb) (fst (fst rec b) Hb)).
  { intros b Hb. exact (snd (IHa b Hb)). }
  econstructor.
  exact (inRectacc A R X IH a Ha rec Hrec).
Defined.

Definition accelim0 (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (X : El1 (arr1 (emb1 A) U01)) (IH : El0 (accelim0_IH A R X))
  (a : El0 A) (h : Acc0 A R a) : El0 (app1 X a).
Proof.
  exact (fst (AccRect A R X IH a h)).
Defined.

Definition accelim0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 Prop0))) (R1 : El0 (arr0 A1 (arr0 A1 Prop0))) (Re : eq0 (arr0 A0 (arr0 A0 Prop0)) (arr0 A1 (arr0 A1 Prop0)) R0 R1)
  (X0 : El1 (arr1 (emb1 A0) U01)) (X1 : El1 (arr1 (emb1 A1) U01)) (Xe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) X0 X1)
  (IH0 : El0 (accelim0_IH A0 R0 X0)) (IH1 : El0 (accelim0_IH A1 R1 X1)) (IHe : eq0 (accelim0_IH A0 R0 X0) (accelim0_IH A1 R1 X1) IH0 IH1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (h0 : Acc0 A0 R0 a0) (h1 : Acc0 A1 R1 a1)
  : eq0 (app1 X0 a0) (app1 X1 a1) (accelim0 A0 R0 X0 IH0 a0 h0) (accelim0 A1 R1 X1 IH1 a1 h1).
Proof.
  unfold accelim0.
  exact (inAccRect_eq A0 A1 Ae R0 R1 Re X0 X1 Xe IH0 IH1 IHe a0 a1 ae h0 h1
           (fst (AccRect A0 R0 X0 IH0 a0 h0)) (fst (AccRect A1 R1 X1 IH1 a1 h1))
           (snd (AccRect A0 R0 X0 IH0 a0 h0)) (snd (AccRect A1 R1 X1 IH1 a1 h1))).
Defined.

(* Quotient types *)

Definition quotient0 (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) : U0.
Proof.
  refine (Quo0 A (fun a b => fst (fst R a) b) (snd R)).
Defined.

Definition quotient0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 Prop0))) (R1 : El0 (arr0 A1 (arr0 A1 Prop0)))
  (Re : eq0 (arr0 A0 (arr0 A0 Prop0)) (arr0 A1 (arr0 A1 Prop0)) R0 R1) :
  eq1 U01 U01 (quotient0 A0 R0) (quotient0 A1 R1).
Proof.
  split.
  - exact Ae.
  - exact Re.
Defined.

Definition quo_in0 (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (a : El0 A) : El0 (quotient0 A R).
Proof.
  exact a.
Defined.

Definition quo_in0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 Prop0))) (R1 : El0 (arr0 A1 (arr0 A1 Prop0)))
  (Re : eq0 (arr0 A0 (arr0 A0 Prop0)) (arr0 A1 (arr0 A1 Prop0)) R0 R1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  : eq0 (quotient0 A0 R0) (quotient0 A1 R1) (quo_in0 A0 R0 a0) (quo_in0 A1 R1 a1).
Proof.
  exists a0. exists a1. split.
  - eapply clo_refl. eapply refl0.
  - split. exact ae. eapply clo_refl. eapply refl0.
Defined.

Definition quo_eq (A : U0) (R : El0 (arr0 A (arr0 A Prop0)))
  (a b : El0 A) (e : fst (fst R a) b) :
  eq0 (quotient0 A R) (quotient0 A R) (quo_in0 A R a) (quo_in0 A R b).
Proof.
  exists b. exists b. split.
  - eapply clo_emb. exact e.
  - split. eapply refl0. eapply clo_refl. eapply refl0.
Defined.

Definition quo_rec0 (A : U0) (R : El0 (arr0 A (arr0 A Prop0))) (P : El1 (arr1 (emb1 (quotient0 A R)) U01))
  (Pq : El0 (pi0 A
               (lam1 (emb1 A) U01
                  (fun a => (app1 P (quo_in0 A R a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A R))) (reflU1 U01) (refl1 _ P)
                                   (quo_in0e A A (reflU0 A) R R (refl0 _ R) a b e))))))
  (Peq : forall (a b : El0 A) (rab : fst (fst R a) b), eq0 (fst P (quo_in0 A R a)) (fst P (quo_in0 A R b)) (fst Pq a) (fst Pq b))
  (x : El0 (quotient0 A R)) : El0 (app1 P x).
Proof.
  exact (fst Pq x).
Defined.

Definition quo_rec0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 Prop0))) (R1 : El0 (arr0 A1 (arr0 A1 Prop0)))
  (Re : eq0 (arr0 A0 (arr0 A0 Prop0)) (arr0 A1 (arr0 A1 Prop0)) R0 R1)
  (P0 : El1 (arr1 (emb1 (quotient0 A0 R0)) U01)) (P1 : El1 (arr1 (emb1 (quotient0 A1 R1)) U01))
  (Pe : eq1 (arr1 (emb1 (quotient0 A0 R0)) U01) (arr1 (emb1 (quotient0 A1 R1)) U01) P0 P1)
  (Pq0 : El0 (pi0 A0
               (lam1 (emb1 A0) U01
                  (fun a => (app1 P0 (quo_in0 A0 R0 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A0 R0))) (reflU1 U01) (refl1 _ P0)
                                   (quo_in0e A0 A0 (reflU0 A0) R0 R0 (refl0 _ R0) a b e))))))
  (Pq1 : El0 (pi0 A1
               (lam1 (emb1 A1) U01
                  (fun a => (app1 P1 (quo_in0 A1 R1 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A1 R1))) (reflU1 U01) (refl1 _ P1)
                                   (quo_in0e A1 A1 (reflU0 A1) R1 R1 (refl0 _ R1) a b e))))))
  (Pqe : eq0 (pi0 A0
               (lam1 (emb1 A0) U01
                  (fun a => (app1 P0 (quo_in0 A0 R0 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A0 R0))) (reflU1 U01) (refl1 _ P0)
                                   (quo_in0e A0 A0 (reflU0 A0) R0 R0 (refl0 _ R0) a b e)))))
           (pi0 A1
               (lam1 (emb1 A1) U01
                  (fun a => (app1 P1 (quo_in0 A1 R1 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A1 R1))) (reflU1 U01) (refl1 _ P1)
                                   (quo_in0e A1 A1 (reflU0 A1) R1 R1 (refl0 _ R1) a b e)))))
           Pq0 Pq1)
  (Peq0 : forall (a b : El0 A0) (rab : fst (fst R0 a) b), eq0 (fst P0 (quo_in0 A0 R0 a)) (fst P0 (quo_in0 A0 R0 b)) (fst Pq0 a) (fst Pq0 b))
  (Peq1 : forall (a b : El0 A1) (rab : fst (fst R1 a) b), eq0 (fst P1 (quo_in0 A1 R1 a)) (fst P1 (quo_in0 A1 R1 b)) (fst Pq1 a) (fst Pq1 b))
  (x0 : El0 (quotient0 A0 R0)) (x1 : El0 (quotient0 A1 R1)) (xe : eq0 (quotient0 A0 R0) (quotient0 A1 R1) x0 x1)
  : eq0 (app1 P0 x0) (app1 P1 x1) (quo_rec0 A0 R0 P0 Pq0 Peq0 x0) (quo_rec0 A1 R1 P1 Pq1 Peq1 x1).
Proof.
  change (eq0 (app1 P0 x0) (app1 P1 x1) (fst Pq0 x0) (fst Pq1 x1)).
  destruct xe as [y0 [y1 [e0 [ey e1]]]].
  assert (eqU0 (app1 P0 x0) (app1 P0 y0)) as eP0.
  { refine (snd P0 x0 y0 _). exists y0. exists y0. split.
    exact e0. split. eapply refl0. eapply clo_refl. eapply refl0. }
  assert (eq0 (app1 P0 x0) (app1 P0 y0) (fst Pq0 x0) (fst Pq0 y0)) as ePxy0.
  { clear Pq1 Pqe Peq1 x1 y1 ey e1 eP0. induction e0.
    - eapply Peq0. exact H.
    - exact (snd Pq0 a b H).
    - eapply sym0. exact IHe0.
    - unshelve refine (trans0 (app1 P0 a) (app1 P0 b) _ (app1 P0 c) IHe0_1 IHe0_2).
      refine (snd P0 a b _). exists b. exists b. split.
      exact e0_1. split. eapply refl0. eapply clo_refl. eapply refl0. }
  assert (eq0 (app1 P0 y0) (app1 P1 y1) (fst Pq0 y0) (fst Pq1 y1)) as ePy.
  { exact (Pqe y0 y1 ey). }
  assert (eqU0 (app1 P1 y1) (app1 P1 x1)) as eP1.
  { refine (snd P1 y1 x1 _). exists x1. exists x1. split.
    exact e1. split. eapply refl0. eapply clo_refl. eapply refl0. }
  assert (eq0 (app1 P1 y1) (app1 P1 x1) (fst Pq1 y1) (fst Pq1 x1)) as ePxy1.
  { clear Pq0 Pqe Peq0 x0 y0 ey e0 eP0 eP1 ePxy0 ePy. induction e1.
    - eapply Peq1. exact H.
    - exact (snd Pq1 a b H).
    - eapply sym0. exact IHe1.
    - unshelve refine (trans0 (app1 P1 a) (app1 P1 b) _ (app1 P1 c) IHe1_1 IHe1_2).
      refine (snd P1 a b _). exists b. exists b. split.
      exact e1_1. split. eapply refl0. eapply clo_refl. eapply refl0. }
  refine (trans0 (app1 P0 x0) (app1 P0 y0) eP0 (app1 P1 x1) ePxy0 _).
  eapply sym0. apply sym0 in ePxy1. apply sym0 in ePy.
  refine (trans0 (app1 P1 x1) (app1 P1 y1) (symU0 _ _ eP1) (app1 P0 y0) ePxy1 ePy).
Defined.
