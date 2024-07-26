(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the definition of our setoid model as a translation from CIC to CIC *)

Set Universe Polymorphism.
Set Primitive Projections.
Set Polymorphic Inductive Cumulativity.
Require Import utils.
Require Import univ0 univ0_lemmas.
Require Import univ1 univ1_lemmas.

(* A context Gamma is an element of U1, and a dependent type over Gamma is an object of `arr1 Gamma U01`
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


(* Sigma types
   The beta and eta equalities are definitionally true *)

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


(* Homogeneous observational equality
   the choice between homogeneous and heterogeneous is purely a matter of taste... *)

Definition obseq0@{i j k l} (A : U0@{i j k}) (a b : El0 A) : El1 Prop01@{i j k l}.
Proof.
  exact (eq0 A A a b).
Defined.

Definition obseq0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (b0 : El0 A0) (b1 : El0 A1) (be : eq0 A0 A1 b0 b1)
  : eq1 Prop01 Prop01 (obseq0 A0 a0 b0) (obseq0 A1 a1 b1).
Proof.
  split.
  - intro e0. pose proof (trans0 A1 A0 (symU0 A0 A1 Ae) A0 (sym0 A0 A1 ae) e0) as e1.
    exact (trans0 A1 A0 (symU0 A0 A1 Ae) A1 e1 be).
  - intro e0. pose proof (trans0 A0 A1 Ae A1 ae e0) as e1.
    exact (trans0 A0 A1 Ae A0 e1 (sym0 A0 A1 be)).
Defined.

Definition obseq_refl0 (A : U0) (a : El0 A) : obseq0 A a a.
Proof.
  exact (refl0 A a).
Defined.

(* NB : here, the result is in Type@{j}
   It should really be in `El2 Prop1` (which is just Type@{j}) but we haven't implemented the universe U2 *)

Definition obseq1@{i j k l} (A : U1@{i j k l}) (a b : El1 A) : Type@{j}.
Proof.
  exact (eq1 A A a b).
Defined.

Definition obseq1e (A0 A1 : U1) (Ae : eqU1 A0 A1)
  (a0 : El1 A0) (a1 : El1 A1) (ae : eq1 A0 A1 a0 a1)
  (b0 : El1 A0) (b1 : El1 A1) (be : eq1 A0 A1 b0 b1)
  : (obseq1 A0 a0 b0) <--> (obseq1 A1 a1 b1).
Proof.
  split.
  - intro e0. pose proof (trans1 A1 A0 (symU1 A0 A1 Ae) A0 (sym1 A0 A1 ae) e0) as e1.
    exact (trans1 A1 A0 (symU1 A0 A1 Ae) A1 e1 be).
  - intro e0. pose proof (trans1 A0 A1 Ae A1 ae e0) as e1.
    exact (trans1 A0 A1 Ae A0 e1 (sym1 A0 A1 be)).
Defined.

Definition obseq_refl1 (A : U1) (a : El1 A) : obseq1 A a a.
Proof.
  exact (refl1 A a).
Defined.

(* Cast operator *)

Definition obseq_cast0 (A B : U0) (e : obseq1 U01 A B) (a : El0 A) : El0 B.
Proof.
  exact (cast0 A B e a).
Defined.

Definition obseq_cast0e (A0 A1 : U0) (Ae : eqU0 A0 A1) (B0 B1 : U0) (Be : eqU0 B0 B1)
  (e0 : obseq1 U01 A0 B0) (e1 : obseq1 U01 A1 B1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1) : eq0 B0 B1 (obseq_cast0 A0 B0 e0 a0) (obseq_cast0 A1 B1 e1 a1).
Proof.
  pose proof (sym0 A0 B0 (cast0_eq A0 B0 e0 a0)) as h0.
  pose proof (trans0 B0 A0 (symU0 A0 B0 e0) A1 h0 ae) as h1.
  refine (trans0 B0 A1 _ B1 h1 (cast0_eq A1 B1 e1 a1)).
  exact (transU0 Be (symU0 A1 B1 e1)).
Defined.

Definition obseq_cast_refl0 (A : U0) (a : El0 A) : obseq0 A a (obseq_cast0 A A (obseq_refl1 U01 A) a).
Proof.
  exact (cast0_eq A A (reflU0 A) a).
Defined.


(* Equality laws: symmetry, transitivity, fapply, proof irrelevance, funext, propext *)

Definition obseq_sym0 (A : U0) (a b : El0 A) : obseq0 A a b -> obseq0 A b a.
Proof.
  apply sym0.
Defined.

Definition obseq_trans0 (A : U0) (a b c : El0 A) : obseq0 A a b -> obseq0 A b c -> obseq0 A a c.
Proof.
  apply trans0. apply reflU0.
Defined.

Definition obseq_ap0 (A B : U0) (f : El0 (arr0 A B)) (a0 a1 : El0 A) :
  obseq0 A a0 a1 -> obseq0 B (fst f a0) (fst f a1).
Proof.
  exact (snd f a0 a1).
Defined.

Definition proof_irr0 (P : El1 Prop01) (p q : P) : obseq0 (emb0 P) p q.
Proof.
  easy.
Defined.

Definition funext0 (A : U0) (P : El1 (arr1 (emb1 A) U01)) (f g : El0 (pi0 A P)) :
  (forall a, obseq0 (fst P a) (fst f a) (fst g a)) -> obseq0 (pi0 A P) f g.
Proof.
  intro H. intros a0 a1 ae.
  exact (trans0 (fst P a0) (fst P a0) (reflU0 _) (fst P a1) (H a0) (snd g a0 a1 ae)).
Defined.

Definition propext0 (P Q : El1 Prop01) : (P <--> Q) -> obseq1 Prop01 P Q.
Proof.
  easy.
Defined.


(* Inductive equality with computation for J on refl *)

Inductive id0@{i j k l} (A : U0@{i j k}) (a : El0@{i j k} A) : El0 A -> Type@{i} :=
| id_refl0 : id0 A a a
| id_obseq0 : forall b, obseq0@{i j k l} A a b -> id0 A a b.

Definition id0_is_obseq0 (A : U0) (a b : El0 A) : id0 A a b <--> obseq0 A a b.
Proof.
  split ; intro H.
  - destruct H. apply refl0. exact o.
  - econstructor. exact H.
Defined.

Definition id0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (b0 : El0 A0) (b1 : El0 A1) (be : eq0 A0 A1 b0 b1)
  : eq1 Prop01 Prop01 (id0 A0 a0 b0) (id0 A1 a1 b1).
Proof.
  change (id0 A0 a0 b0 <--> id0 A1 a1 b1).
  eapply biimpl_trans. apply id0_is_obseq0.
  eapply biimpl_trans. apply (obseq0e A0 A1 Ae a0 a1 ae b0 b1 be).
  eapply biimpl_sym. apply id0_is_obseq0.
Defined.

Definition J0 (A : U0) (a : El0 A)
  (P : El1 (Pi1 (emb1 A) (fun b => arr1 (emb1 (emb0 (id0 A a b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A A (reflU0 A) a a (refl0 A a) b0 b1 be) (fun _ _ _ => I))))
  (t : El0 (fst (fst P a) (id_refl0 A a))) (b : El0 A) (e : id0 A a b)
  : El0 (fst (fst P b) e).
Proof.
  destruct e as [ | b e ].
  - exact t.
  - refine (cast0 (fst (fst P a) (id_refl0 A a)) (fst (fst P b) (id_obseq0 A a b e)) _ t).
    refine (snd P a b e (id_refl0 A a) (id_obseq0 A a b e) I).
Defined.

Definition J0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (P0 : El1 (Pi1 (emb1 A0) (fun b => arr1 (emb1 (emb0 (id0 A0 a0 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A0 A0 (reflU0 A0) a0 a0 (refl0 A0 a0) b0 b1 be) (fun _ _ _ => I))))
  (P1 : El1 (Pi1 (emb1 A1) (fun b => arr1 (emb1 (emb0 (id0 A1 a1 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A1 A1 (reflU0 A1) a1 a1 (refl0 A1 a1) b0 b1 be) (fun _ _ _ => I))))
  (Pe : eq1 (Pi1 (emb1 A0) (fun b => arr1 (emb1 (emb0 (id0 A0 a0 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A0 A0 (reflU0 A0) a0 a0 (refl0 A0 a0) b0 b1 be) (fun _ _ _ => I)))
            (Pi1 (emb1 A1) (fun b => arr1 (emb1 (emb0 (id0 A1 a1 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A1 A1 (reflU0 A1) a1 a1 (refl0 A1 a1) b0 b1 be) (fun _ _ _ => I)))
            P0 P1)
  (t0 : El0 (fst (fst P0 a0) (id_refl0 A0 a0))) (t1 : El0 (fst (fst P1 a1) (id_refl0 A1 a1)))
  (te : eq0 (fst (fst P0 a0) (id_refl0 A0 a0)) (fst (fst P1 a1) (id_refl0 A1 a1)) t0 t1)
  (b0 : El0 A0) (b1 : El0 A1) (be : eq0 A0 A1 b0 b1)
  (e0 : id0 A0 a0 b0) (e1 : id0 A1 a1 b1)
  : eq0 (fst (fst P0 b0) e0) (fst (fst P1 b1) e1) (J0 A0 a0 P0 t0 b0 e0) (J0 A1 a1 P1 t1 b1 e1).
Proof.
  destruct e0 as [ | b0 e0 ].
  - destruct e1 as [ | b1 e1 ].
    + exact te.
    + refine (trans0 (fst (fst P0 a0) (id_refl0 A0 a0)) (fst (fst P1 a1) (id_refl0 A1 a1)) _ (fst (fst P1 b1) (id_obseq0 A1 a1 b1 e1)) te _).
      exact (Pe a0 a1 ae (id_refl0 A0 a0) (id_refl0 A1 a1) I).
      exact (cast0_eq (fst (fst P1 a1) (id_refl0 A1 a1)) (fst (fst P1 b1) (id_obseq0 A1 a1 b1 e1)) _ t1).
  - destruct e1 as [ | b1 e1 ].
    + refine (trans0 (fst (fst P0 b0) (id_obseq0 A0 a0 b0 e0)) (fst (fst P0 a0) (id_refl0 A0 a0)) _ (fst (fst P1 a1) (id_refl0 A1 a1)) _ te).
      exact (snd P0 b0 a0 (sym0 _ _ e0) (id_obseq0 A0 a0 b0 e0) (id_refl0 A0 a0) I).
      exact (sym0 _ _ (cast0_eq (fst (fst P0 a0) (id_refl0 A0 a0)) (fst (fst P0 b0) (id_obseq0 A0 a0 b0 e0)) _ t0)).
    + refine (trans0 (fst (fst P0 b0) (id_obseq0 A0 a0 b0 e0)) (fst (fst P0 a0) (id_refl0 A0 a0)) _ (fst (fst P1 b1) (id_obseq0 A1 a1 b1 e1)) _ _).
      exact (snd P0 b0 a0 (sym0 _ _ e0) (id_obseq0 A0 a0 b0 e0) (id_refl0 A0 a0) I).
      exact (sym0 _ _ (cast0_eq (fst (fst P0 a0) (id_refl0 A0 a0)) (fst (fst P0 b0) (id_obseq0 A0 a0 b0 e0)) _ t0)).
      refine (trans0 (fst (fst P0 a0) (id_refl0 A0 a0)) (fst (fst P1 a1) (id_refl0 A1 a1)) _ (fst (fst P1 b1) (id_obseq0 A1 a1 b1 e1)) te _).
      exact (Pe a0 a1 ae (id_refl0 A0 a0) (id_refl0 A1 a1) I).
      exact (cast0_eq (fst (fst P1 a1) (id_refl0 A1 a1)) (fst (fst P1 b1) (id_obseq0 A1 a1 b1 e1)) _ t1).
Defined.

Definition J_on_refl0 (A : U0) (a : El0 A)
  (P : El1 (Pi1 (emb1 A) (fun b => arr1 (emb1 (emb0 (id0 A a b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A A (reflU0 A) a a (refl0 A a) b0 b1 be) (fun _ _ _ => I))))
  (t : El0 (fst (fst P a) (id_refl0 A a)))
  : J0 A a P t a (id_refl0 A a) = t.
Proof.
  reflexivity.
Defined.

Definition J_on_refl0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (P0 : El1 (Pi1 (emb1 A0) (fun b => arr1 (emb1 (emb0 (id0 A0 a0 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A0 A0 (reflU0 A0) a0 a0 (refl0 A0 a0) b0 b1 be) (fun _ _ _ => I))))
  (P1 : El1 (Pi1 (emb1 A1) (fun b => arr1 (emb1 (emb0 (id0 A1 a1 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A1 A1 (reflU0 A1) a1 a1 (refl0 A1 a1) b0 b1 be) (fun _ _ _ => I))))
  (Pe : eq1 (Pi1 (emb1 A0) (fun b => arr1 (emb1 (emb0 (id0 A0 a0 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A0 A0 (reflU0 A0) a0 a0 (refl0 A0 a0) b0 b1 be) (fun _ _ _ => I)))
            (Pi1 (emb1 A1) (fun b => arr1 (emb1 (emb0 (id0 A1 a1 b))) U01)
                (fun b0 b1 be => mkAndEx (id0e A1 A1 (reflU0 A1) a1 a1 (refl0 A1 a1) b0 b1 be) (fun _ _ _ => I)))
            P0 P1)
  (t0 : El0 (fst (fst P0 a0) (id_refl0 A0 a0))) (t1 : El0 (fst (fst P1 a1) (id_refl0 A1 a1)))
  (te : eq0 (fst (fst P0 a0) (id_refl0 A0 a0)) (fst (fst P1 a1) (id_refl0 A1 a1)) t0 t1)
  : J0e A0 A1 Ae a0 a1 ae P0 P1 Pe t0 t1 te a0 a1 ae (id_refl0 A0 a0) (id_refl0 A1 a1) = te.
Proof.
  reflexivity.
Defined.


(* Quotient types à la Hofmann *)

Definition quotient0 (A : U0) (R : El1 (arr1 (emb1 A) (arr1 (emb1 A) Prop01))) : U0.
Proof.
  refine (Quo0 A (fun a b => fst (fst R a) b) (snd R)).
Defined.

Definition quotient0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El1 (arr1 (emb1 A0) (arr1 (emb1 A0) Prop01))) (R1 : El1 (arr1 (emb1 A1) (arr1 (emb1 A1) Prop01)))
  (Re : eq1 (arr1 (emb1 A0) (arr1 (emb1 A0) Prop01)) (arr1 (emb1 A1) (arr1 (emb1 A1) Prop01)) R0 R1) :
  eq1 U01 U01 (quotient0 A0 R0) (quotient0 A1 R1).
Proof.
  split.
  - exact Ae.
  - exact Re.
Defined.

Definition quo_in0 (A : U0) (R : El1 (arr1 (emb1 A) (arr1 (emb1 A) Prop01))) (a : El0 A) : El0 (quotient0 A R).
Proof.
  exact a.
Defined.

Definition quo_in0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El1 (arr1 (emb1 A0) (arr1 (emb1 A0) Prop01))) (R1 : El1 (arr1 (emb1 A1) (arr1 (emb1 A1) Prop01)))
  (Re : eq1 (arr1 (emb1 A0) (arr1 (emb1 A0) Prop01)) (arr1 (emb1 A1) (arr1 (emb1 A1) Prop01)) R0 R1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  : eq0 (quotient0 A0 R0) (quotient0 A1 R1) (quo_in0 A0 R0 a0) (quo_in0 A1 R1 a1).
Proof.
  exists a0. exists a1. split.
  - eapply clo_refl. eapply refl0.
  - split. exact ae. eapply clo_refl. eapply refl0.
Defined.

Definition quo_eq (A : U0) (R : El1 (arr1 (emb1 A) (arr1 (emb1 A) Prop01)))
  (a b : El0 A) (e : fst (fst R a) b) :
  eq0 (quotient0 A R) (quotient0 A R) (quo_in0 A R a) (quo_in0 A R b).
Proof.
  exists b. exists b. split.
  - eapply clo_emb. exact e.
  - split. eapply refl0. eapply clo_refl. eapply refl0.
Defined.

Definition quo_rec0 (A : U0) (R : El1 (arr1 (emb1 A) (arr1 (emb1 A) Prop01))) (P : El1 (arr1 (emb1 (quotient0 A R)) U01))
  (Pq : El0 (pi0 A
               (lam1 (emb1 A) U01
                  (fun a => (app1 P (quo_in0 A R a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A R))) (reflU1 U01) (refl1 _ P)
                                   (quo_in0e A A (reflU0 A) R R (refl1 _ R) a b e))))))
  (Peq : forall (a b : El0 A) (rab : fst (fst R a) b), eq0 (fst P (quo_in0 A R a)) (fst P (quo_in0 A R b)) (fst Pq a) (fst Pq b))
  (x : El0 (quotient0 A R)) : El0 (app1 P x).
Proof.
  exact (fst Pq x).
Defined.

Definition quo_rec0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El1 (arr1 (emb1 A0) (arr1 (emb1 A0) Prop01))) (R1 : El1 (arr1 (emb1 A1) (arr1 (emb1 A1) Prop01)))
  (Re : eq1 (arr1 (emb1 A0) (arr1 (emb1 A0) Prop01)) (arr1 (emb1 A1) (arr1 (emb1 A1) Prop01)) R0 R1)
  (P0 : El1 (arr1 (emb1 (quotient0 A0 R0)) U01)) (P1 : El1 (arr1 (emb1 (quotient0 A1 R1)) U01))
  (Pe : eq1 (arr1 (emb1 (quotient0 A0 R0)) U01) (arr1 (emb1 (quotient0 A1 R1)) U01) P0 P1)
  (Pq0 : El0 (pi0 A0
               (lam1 (emb1 A0) U01
                  (fun a => (app1 P0 (quo_in0 A0 R0 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A0 R0))) (reflU1 U01) (refl1 _ P0)
                                   (quo_in0e A0 A0 (reflU0 A0) R0 R0 (refl1 _ R0) a b e))))))
  (Pq1 : El0 (pi0 A1
               (lam1 (emb1 A1) U01
                  (fun a => (app1 P1 (quo_in0 A1 R1 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A1 R1))) (reflU1 U01) (refl1 _ P1)
                                   (quo_in0e A1 A1 (reflU0 A1) R1 R1 (refl1 _ R1) a b e))))))
  (Pqe : eq0 (pi0 A0
               (lam1 (emb1 A0) U01
                  (fun a => (app1 P0 (quo_in0 A0 R0 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A0 R0))) (reflU1 U01) (refl1 _ P0)
                                   (quo_in0e A0 A0 (reflU0 A0) R0 R0 (refl1 _ R0) a b e)))))
           (pi0 A1
               (lam1 (emb1 A1) U01
                  (fun a => (app1 P1 (quo_in0 A1 R1 a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A1 R1))) (reflU1 U01) (refl1 _ P1)
                                   (quo_in0e A1 A1 (reflU0 A1) R1 R1 (refl1 _ R1) a b e)))))
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
  { clear Pq1 Pqe Peq1 x1 y1 ey e1 eP0. induction e0 as [a b H | a b H | H | a b c e0_1 IHe0_1 e0_2 IHe0_2 ].
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
  { clear Pq0 Pqe Peq0 x0 y0 ey e0 eP0 eP1 ePxy0 ePy. induction e1 as [a b H | a b H | H | a b c e1_1 IHe1_1 e1_2 IHe1_2 ].
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

(* Truncation operator *)

Definition trunc0@{i j k l} : El1 U01@{i j k l} -> El1 Prop01@{i j k l}.
Proof.
  exact El0.
Defined.

Definition trunc0e (A0 A1 : El1 U01) (Ae : eq1 U01 U01 A0 A1) : eq1 Prop01 Prop01 (trunc0 A0) (trunc0 A1).
Proof.
  split.
  - intro a. exact (cast0 A0 A1 Ae a).
  - intro a. exact (cast0 A1 A0 (symU0 _ _ Ae) a).
Defined.

(* Unique choice allows us to escape truncations for HProps *)

Definition untrunc0@{i j k l} (A : El1 U01@{i j k l}) (HA : forall (a b : El0 A), obseq0@{i j k l} A a b)
  : trunc0@{i j k l} A -> El0@{i j k} A.
Proof.
  intro a. exact a.
Defined.

Definition untrunc0e (A0 A1 : El1 U01) (Ae : eq1 U01 U01 A0 A1)
  (HA0 : forall (a b : El0 A0), obseq0 A0 a b) (HA1 : forall (a b : El0 A1), obseq0 A1 a b)
  (a0 : trunc0 A0) (a1 : trunc0 A1) : eq0 A0 A1 (untrunc0 A0 HA0 a0) (untrunc0 A1 HA1 a1).
Proof.
  refine (trans0 A0 A1 Ae A1 (cast0_eq A0 A1 Ae a0) (HA1 _ _)).
Defined.
