(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains a proof that
 - the equality eqU1 on U1 is reflexive, symmetric and transitive
 - the heterogeneous equality eq1 is reflexive, symmetric and transitive
 - there is a cast operator between equal types that preserves the equality
*)

Set Universe Polymorphism.
Set Primitive Projections.
Require Import utils.
Require Import univ0 univ0_lemmas.
Require Import univ1.

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
