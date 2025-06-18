(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains a proof that
 - the equality eqU0 on U0 is reflexive, symmetric and transitive
 - the heterogeneous equality eq0 is reflexive, symmetric and transitive
 - there is a cast operator between equal types that preserves the equality
*)

Set Universe Polymorphism.
Set Primitive Projections.
Require Import utils.
Require Import univ0.

Definition refl0 (A : U0) (a : El0 A) : eq0 A A a a.
Proof.
  revert a. pattern A ; eapply U0_ind.
  - easy.
  - exact nateq_refl.
  - intros a. split ; easy.
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
  - clear A. intros A IHA a b p. exact stt.
Defined.

Definition reflU0 (A : U0) : eqU0 A A.
Proof.
  pattern A ; eapply U0_ind ; try (now econstructor).
  - clear A. intros A IHA a b. constructor.
    + assumption.
    + constructor ; eapply refl0.
Defined.

Definition sym0_pre (A B : U0) {a : El0 A} {b : El0 B} : sand (eq0 A B a b -> eq0 B A b a) (eq0 B A b a -> eq0 A B a b).
Proof.
  revert B a b. pattern A ; eapply U0_ind ; clear A.
  - intros P B ; pattern B ; eapply U0_ind ; clear B.
    2,3,4,5,6,7,8: intros ; split ; now intros [].
    intros Q p q. easy.
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,3,4,5,6,7,8: intros ; split ; now intros [].
    intros a b. split ; exact nateq_sym.
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,4,5,6,7,8: intros ; split ; now intros [].
    intros a b. split.
    + intro H. split. exact (sand_snd H). exact (sand_fst H).
    + intro H. split. exact (sand_snd H). exact (sand_fst H).
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,5,6,7,8: intros ; split ; now intros [].
    intros B _ Q _ Qe t u. split.
    + intros [ eap epq ]. split.
      * apply IHA. exact eap.
      * apply IHP. exact epq.
    + intros [ eap epq ]. split.
      * apply IHA. exact eap.
      * apply IHP. exact epq.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,6,7,8: intros ; split ; now intros [].
    intros B _ Q _ Qe f g. split.
    + intros e b a eba. eapply IHP. apply (sand_snd (IHA B a b)) in eba. exact (e a b eba).
    + intros e a b eab. eapply IHP. apply (sand_fst (IHA B a b)) in eab. exact (e b a eab).
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,7,8: intros ; split ; now intros [].
    intros B _ Q _ Qe.
    change (forall (w0 : El0 (W0 A P Pe)) (w1 : El0 (W0 B Q Qe)),
               sand ((Weq (eq0 A B) (fun a b => eq0 (P a) (Q b)) (fst w0) (fst w1))
                     -> (Weq (eq0 B A) (fun b a => eq0 (Q b) (P a)) (fst w1) (fst w0)))
                 ((Weq (eq0 B A) (fun b a => eq0 (Q b) (P a)) (fst w1) (fst w0))
                  -> (Weq (eq0 A B) (fun a b => eq0 (P a) (Q b)) (fst w0) (fst w1)))).
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
    1,2,3,4,5,6,8: intros ; split ; now intros [].
    intros B _ S Se. intros a b. split.
    + intros [ a1 [ b1 [ ae [ e be ] ] ] ].
      exists b1. exists a1. split. exact (clo_sym _ _ be).
      split. apply (IHA B a1 b1). exact e. exact (clo_sym _ _ ae).
    + intros [ b1 [ a1 [ be [ e ae ] ] ] ].
      exists a1. exists b1. split. exact (clo_sym _ _ ae).
      split. apply (IHA B a1 b1). exact e. exact (clo_sym _ _ be).
  - intros A IHA a b. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,6,7: intros ; split ; now intros [].
    intros B _ c d p q. constructor ; easy.
Defined.

Definition sym0 (A B : U0) {a : El0 A} {b : El0 B} : eq0 A B a b -> eq0 B A b a.
Proof.
  intro e. eapply (sym0_pre A B). exact e.
Defined.

Definition symU0_pre (A B : U0) : sand (eqU0 A B -> eqU0 B A) (eqU0 B A -> eqU0 A B).
Proof.
  revert B. pattern A ; eapply U0_ind ; clear A.
  - intro P. intro B ; pattern B ; eapply U0_ind ; clear B.
    2,3,4,5,6,7,8: split ; now intros [].
    intro Q. split.
    + intro H. split. exact (sand_snd H). exact (sand_fst H).
    + intro H. split. exact (sand_snd H). exact (sand_fst H).
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,3,4,5,6,7,8: split ; now intros [].
    easy.
  - intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,4,5,6,7,8: split ; now intros [].
    easy.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,5,6,7,8: split ; now intros [].
    intros B _ Q _ Qe. split.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,6,7,8: split ; now intros [].
    intros B _ Q _ Qe. split.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
  - intros A IHA P IHP Pe. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,7,8: split ; now intros [].
    intros B _ Q _ Qe. split.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
    + intros [ eAB ePQ ]. apply IHA in eAB. econstructor.
      exact eAB. intros a b eab. eapply IHP. eapply ePQ. eapply sym0. exact eab.
  - intros A IHA R Re. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,6,8: split ; now intros [].
    intros B _ S Se. split.
    + intros [ eAB eRS ]. apply IHA in eAB. econstructor.
      exact eAB. intros a0 b0 e0 a1 b1 e1. split.
      * refine (sand_snd (eRS b0 a0 (sym0 _ _ e0) b1 a1 (sym0 _ _ e1))).
      * refine (sand_fst (eRS b0 a0 (sym0 _ _ e0) b1 a1 (sym0 _ _ e1))).
    + intros [ eBA eSR ]. apply IHA in eBA. econstructor.
      exact eBA. intros a0 b0 e0 a1 b1 e1. split.
      * refine (sand_snd (eSR b0 a0 (sym0 _ _ e0) b1 a1 (sym0 _ _ e1))).
      * refine (sand_fst (eSR b0 a0 (sym0 _ _ e0) b1 a1 (sym0 _ _ e1))).
  - intros A IHA a b. intro B ; pattern B ; eapply U0_ind ; clear B.
    1,2,3,4,5,6,7: split ; now intros [].
    intros B _ c d. split.
    + intros [ eAB [ eac ebd ] ]. split. apply IHA. exact eAB.
      split. apply sym0. exact eac. apply sym0. exact ebd.
    + intros [ eBA [ eca edb ] ]. split. apply IHA. exact eBA.
      split. apply sym0. exact eca. apply sym0. exact edb.
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
  (R : El0 A -> El0 A -> SProp) (S : El0 B -> El0 B -> SProp)
  (Re : forall a0 a1 (ae : eq0 A A a0 a1) b0 b1 (be : eq0 A A b0 b1), sand (R a0 b0 -> R a1 b1) (R a1 b1 -> R a0 b0))
  (Se : forall a0 a1 (ae : eq0 B B a0 a1) b0 b1 (be : eq0 B B b0 b1), sand (S a0 b0 -> S a1 b1) (S a1 b1 -> S a0 b0))
  (eRS : forall a0 b0 (e0 : eq0 A B a0 b0) a1 b1 (e1 : eq0 A B a1 b1), sand (R a0 a1 -> S b0 b1) (S b0 b1 -> R a0 a1))
  : forall a0 b0 (e0 : eq0 A B a0 b0) a1 b1 (e1 : eq0 A B a1 b1), sand (closure (eq0 A A) R a0 a1 -> closure (eq0 B B) S b0 b1) (closure (eq0 B B) S b0 b1 -> closure (eq0 A A) R a0 a1).
Proof.
  intros a0 b0 e0 a1 b1 e1. split.
  - intro Ha. revert b0 e0 b1 e1. induction Ha.
    + intros b0 e0 b1 e1. eapply clo_emb. eapply (eRS a b0 e0 b b1 e1). exact r.
    + intros b0 e0 b1 e1. pose proof (transb IH B (transb IH A (sym0 _ _ e0) e) e1) as be.
      eapply clo_refl. exact be.
    + intros b0 e0 b1 e1. eapply clo_sym. eapply IHHa. exact e1. exact e0.
    + intros b0 e0 b1 e1. set (b2 := castf IH b). eapply (clo_trans b0 b2 b1).
      * eapply (IHHa1 b0 e0 b2). exact (castf_eq IH b).
      * unshelve eapply (IHHa2 b2 _ b1 e1). exact (castf_eq IH b).
  - intro Hb. revert a0 e0 a1 e1. induction Hb.
    + intros a0 e0 a1 e1. eapply clo_emb. eapply (eRS a0 a e0 a1 b e1). exact r.
    + intros a0 e0 a1 e1. pose proof (transf IH A (transf IH B e0 e) (sym0 _ _ e1)) as ae.
      eapply clo_refl. exact ae.
    + intros a0 e0 a1 e1. eapply clo_sym. eapply IHHb. exact e1. exact e0.
    + intros a0 e0 a1 e1. set (a2 := castb IH b). eapply (clo_trans a0 a2 a1).
      * eapply (IHHb1 a0 e0 a2). exact (sym0 _ _ (castb_eq IH b)).
      * unshelve eapply (IHHb2 a2 _ a1 e1). exact (sym0 _ _ (castb_eq IH b)).
Defined.

Definition iff_trans_s
     : forall A B C : SProp, sand (A -> B) (B -> A) -> sand (B -> C) (C -> B) -> sand (A -> C) (C -> A).
  intros. split.
  - intro a. apply (sand_fst H0). apply (sand_fst H). exact a.
  - intro c. apply (sand_snd H). apply (sand_snd H0). exact c.
Defined.

Definition cast_lemmas@{i j} (A : U0@{i j}) (B : U0@{i j}) (e : eqU0 A B) : cast_lemmas_conclusion@{i j} A B e.
Proof.
  eapply U0_rect2 ; clear A B e.
  (* emb *)
  - unshelve econstructor.
    + intro p. eapply to_set_intro. eapply (sand_fst e). destruct p. exact a.
    + intro q. eapply to_set_intro. eapply (sand_snd e). destruct q. exact a.
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
      intros a b c. eapply iff_trans_s.
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros a b c. eapply iff_trans_s.
    + intros. split ; easy.
    + intros. split ; easy.
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
      * refine (clo_trans _ _ _ ae _).
        apply (closure_eqrel A B eAB IHA R S Re Se eRS a1 b1 eab (castb IHA b2) b2 (sym0 _ _ (castb_eq IHA b2))).
        exact (clo_trans _ _ _ be1 be2).
      * split. refine (transf IHA C _ ebc). apply sym0. exact (castb_eq IHA b2). exact ce.
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
      intros C _ T Te a b c [ b1 [ a1 [ be [ eab ae1 ] ] ] ] [ a2 [ c1 [ ae2 [ eac ce ] ] ] ].
      exists (castf IHA a2). exists c1. split.
      * refine (clo_trans _ _ _ be _).
        apply (closure_eqrel A B eAB IHA R S Re Se eRS a1 b1 (sym0 _ _ eab) a2 (castf IHA a2) (castf_eq IHA a2)).
        exact (clo_trans _ _ _ ae1 ae2).
      * split. refine (transb IHA C _ eac). apply sym0. exact (castf_eq IHA a2). exact ce.
    + intros a. exists a. exists (castf IHA a). split.
      * eapply clo_refl. eapply refl0.
      * split. exact (castf_eq IHA a). eapply clo_refl. eapply refl0.
    + intros b. exists b. exists (castb IHA b). split.
      * eapply clo_refl. eapply refl0.
      * split. exact (castb_eq IHA b). eapply clo_refl. eapply refl0.
  (* Identity types *)
  - intros A B eAB IHA a b c d eac ebd. unshelve econstructor.
    + intro p. refine (forded _).
      refine (transb IHA B (sym0 A B eac) _).
      refine (sym0 B A (transb IHA A (sym0 A B ebd) (sym0 A A _))).
      exact (obseq_of_fordedId (El0 A) (eq0 A A) (refl0 A) a b p).
    + intro p. refine (forded _).
      refine (transf IHA A eac _).
      refine (sym0 A B (transf IHA B ebd (sym0 B B _))).
      exact (obseq_of_fordedId (El0 B) (eq0 B B) (refl0 B) c d p).
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
    + intro C. pattern C ; eapply U0_ind ; clear C ; try easy.
    + intros. exact stt.
    + intros. exact stt.
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
  eapply U0_ind2 ; clear eAB B A.
  - intros P Q ePQ. intro C.
    pattern C ; eapply U0_ind ; clear C ; try easy.
    intros R eQR. exact (iff_trans_s _ _ _ ePQ eQR).
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
      exact (iff_trans_s _ _ _ (eRS a0 b0 eab0 a1 b1 eab1) (eST b0 c0 ebc0 b1 c1 ebc1)).
  - intros A B eAB IHA a b c d eac ebd. intro C.
    pattern C ; eapply U0_ind ; clear C ; try easy.
    intros C _ f g [ eBC [ ecf edg ] ]. split.
    + exact (IHA C eBC).
    + split. exact (trans0 A B eAB C eac ecf). exact (trans0 A B eAB C ebd edg).
Defined.
