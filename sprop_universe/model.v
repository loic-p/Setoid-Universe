(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the bricks of our setoid model *)

Set Universe Polymorphism.
Set Primitive Projections.
Require Import utils.
Require Import univ0 univ0_lemmas.
Require Import univ1 univ1_lemmas.

(* Nondependent functions in the upper universe *)

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

(* Dependent functions in the lower universe *)

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
  exact (mkPairs t te).
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
  (t : El0 (sigma0 A P)) : El0 (fsts P (fst0 t)).
Proof.
  exact (snd t).
Defined.

Definition snd0e {A0 A1 : El1 U01} (Ae : eqU0 A0 A1)
  {P0 : El1 (arr1 (emb1 A0) U01)} {P1 : El1 (arr1 (emb1 A1) U01)} (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  {t0 : El0 (sigma0 A0 P0)} {t1 : El0 (sigma0 A1 P1)} {te : eq0 (sigma0 A0 P0) (sigma0 A1 P1) t0 t1}
  : eq0 (fsts P0 (fst0 t0)) (fsts P1 (fst0 t1)) (snd0 t0) (snd0 t1).
Proof.
  exact (andright te).
Defined.


(* Impredicative quantification *)

Definition forall0 (A : El1 U01) (P : El0 (arr0 A SProp0)) : El0 SProp0.
Proof.
  destruct P as [ P Pe ].
  exact (forall (a : El0 A), P a).
Defined.

Definition forall0e {A B : El1 U01} (eAB : eq1 U01 U01 A B)
  {P : El0 (arr0 A SProp0)} {Q : El0 (arr0 B SProp0)} (ePQ : eq0 (arr0 A SProp0) (arr0 B SProp0) P Q)
  : eq0 SProp0 SProp0 (forall0 A P) (forall0 B Q).
Proof.
  destruct P as [ P Pe ]. destruct Q as [ Q Qe ].
  unshelve econstructor.
  - intros f b. set (a := cast0 B A (symU0 A B eAB) b).
    pose proof (cast0_eq B A (symU0 A B eAB) b) as eab. change (eq0 B A b a) in eab.
    pose proof (ePQ a b (sym0 B A eab)) as e0. change (sand ((P a) -> (Q b)) ((Q b) -> (P a))) in e0.
    destruct e0 as [ H _ ]. exact (H (f a)).
  - intros f a. set (b := cast0 A B eAB a).
    pose proof (cast0_eq A B eAB a) as eab. change (eq0 A B a b) in eab.
    pose proof (ePQ a b eab) as e0. change (sand (P a -> Q b) (Q b -> P a)) in e0.
    destruct e0 as [ _ H ]. exact (H (f b)).
Defined.

Definition forall_app0 {A : El1 U01} {P : El0 (arr0 A SProp0)} (f : (forall0 A P)) (a : El0 A) : (fsts P a).
Proof.
  exact (f a).
Defined.

Definition forall_lam0 (A : El1 U01) (P : El0 (arr0 A SProp0))
  (t : forall a : El0 A, fsts P a) : forall0 A P.
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
  refine (nat_rect (fun n => El0 (app1 P n)) Pz (fun m Pn => fsts ((fsts Ps) m) Pn) n).
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
  - exact (sup a (fun p => fst (fsts f p))).
  - exact (extsup a (fun p => fst (fsts f p)) (fun p => snd (fsts f p)) (snds f)).
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
                            (fun f => arr0 (Pi0 (app1 P a) (fun p => app1 X (fsts f p)) _) (app1 X (sup0 A P a f))) _) _).
  - intros p0 p1 pe. exact (snds X (fsts f p0) (fsts f p1) (snds f p0 p1 pe)).
  - intros f0 f1 fe. eapply arr0e.
    + constructor.
      * apply reflU0.
      * intros p0 p1 pe. exact (snds X (fsts f0 p0) (fsts f1 p1) (fe p0 p1 pe)).
    + refine (snds X (sup0 A P a f0) (sup0 A P a f1) _). constructor.
      * apply refl0.
      * intros p0 p1 pe. exact (fe p0 p1 pe).
  - intros a0 a1 ae. constructor.
    + eapply arr0e.
      * exact (snds P a0 a1 ae).
      * apply reflU0.
    + intros f0 f1 fe. eapply arr0e.
      * constructor.
        ** exact (snds P a0 a1 ae).
        ** intros p0 p1 pe. exact (snds X _ _ (fe p0 p1 pe)).
      * refine (snds X (sup0 A P a0 f0) (sup0 A P a1 f1) _). constructor.
        ** exact ae.
        ** intros p0 p1 pe. exact (fe p0 p1 pe).
Defined.

Inductive inWRect (A : U0) (P : El1 (arr1 (emb1 A) U01)) (X : El1 (arr1 (emb1 (Wtype0 A P)) U01)) (IH : El0 (welim0_IH A P X))
  : forall (w : El0 (Wtype0 A P)) (x : El0 (fsts X w)), Type :=
| inRectsup : forall (a : El0 A) (f : El0 (arr0 (app1 P a) (Wtype0 A P)))
                     (rec : El0 (Pi0 (app1 P a) (fun p => fsts X (fsts f p)) (fun p0 p1 pe => snds X _ _ (snds f p0 p1 pe))))
                     (Hrec : forall (p : El0 (app1 P a)), inWRect A P X IH (fsts f p) (fsts rec p))
  , inWRect A P X IH (sup0 A P a f) (fsts (fsts (fsts IH a) f) rec).

Definition inWRect_eq (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (P0 : El1 (arr1 (emb1 A0) U01)) (P1 : El1 (arr1 (emb1 A1) U01)) (Pe : eq1 (arr1 (emb1 A0) U01) (arr1 (emb1 A1) U01) P0 P1)
  (X0 : El1 (arr1 (emb1 (Wtype0 A0 P0)) U01)) (X1 : El1 (arr1 (emb1 (Wtype0 A1 P1)) U01))
  (Xe : eq1 (arr1 (emb1 (Wtype0 A0 P0)) U01) (arr1 (emb1 (Wtype0 A1 P1)) U01) X0 X1)
  (IH0 : El0 (welim0_IH A0 P0 X0)) (IH1 : El0 (welim0_IH A1 P1 X1)) (IHe : eq0 (welim0_IH A0 P0 X0) (welim0_IH A1 P1 X1) IH0 IH1)
  : forall (w0 : El0 (Wtype0 A0 P0)) (w1 : El0 (Wtype0 A1 P1)) (we : eq0 (Wtype0 A0 P0) (Wtype0 A1 P1) w0 w1)
           (x0 : El0 (fsts X0 w0)) (x1 : El0 (fsts X1 w1))
           (Hx0 : inWRect A0 P0 X0 IH0 w0 x0) (Hx1 : inWRect A1 P1 X1 IH1 w1 x1)
  , eq0 (fsts X0 w0) (fsts X1 w1) x0 x1.
Proof.
  intros w0 w1 we x0 x1 Hx0. revert w1 we x1. induction Hx0 as [ a0 f0 rec0 Hrec0 IHx0 ].
  intros w1 we x1 Hx1. destruct Hx1 as [ a1 f1 rec1 Hrec1 ].
  change (Weq (eq0 A0 A1) (fun a0 a1 => eq0 (fsts P0 a0) (fsts P1 a1)) (fst (sup0 A0 P0 a0 f0)) (fst (sup0 A1 P1 a1 f1))) in we.
  apply Weq_inversion in we. destruct we as [ ae fe ].
  refine (IHe a0 a1 ae f0 f1 fe rec0 rec1 _).
  change (forall p0 p1 (pe : eq0 (app1 P0 a0) (app1 P1 a1) p0 p1)
           , (eq0 (app1 X0 (fsts f0 p0)) (app1 X1 (fsts f1 p1)) (fsts rec0 p0) (fsts rec1 p1))).
  intros p0 p1 pe.
  refine (IHx0 p0 (fsts f1 p1) (fe p0 p1 pe) (fsts rec1 p1) (Hrec1 p1)).
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
  unshelve epose (rec := _ : El0 (Pi0 (app1 P a) (fun p => fsts X (fsts f0 p)) (fun p0 p1 pe => snds X _ _ (snds f0 p0 p1 pe)))).
  { unshelve econstructor.
    - intro p. exact (fst (IHf p)).
    - intros p0 p1 pe. refine (inWRect_eq A A (reflU0 A) P P (refl1 (arr1 (emb1 A) U01) P)
                                 X X (refl1 (arr1 (emb1 (Wtype0 A P)) U01) X) IH IH (refl0 (welim0_IH A P X) IH)
                                 (fsts f0 p0) (fsts f0 p1) (snds f0 p0 p1 pe) _ _ _ _).
      + exact (snd (IHf p0)).
      + exact (snd (IHf p1)). }
  unshelve epose (Hrec := _ : forall (p : El0 (app1 P a)), inWRect A P X IH (fsts f0 p) (fsts rec p)).
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

Definition obseq0 (A : U0) (a b : El0 A) : El0 SProp0.
Proof.
  exact (eq0 A A a b).
Defined.

Definition obseq0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  (b0 : El0 A0) (b1 : El0 A1) (be : eq0 A0 A1 b0 b1)
  : eq0 SProp0 SProp0 (obseq0 A0 a0 b0) (obseq0 A1 a1 b1).
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

Definition obseq1 (A : U1) (a b : El1 A) : El0 SProp0.
Proof.
  exact (eq1 A A a b).
Defined.

Definition obseq1e (A0 A1 : U1) (Ae : eqU1 A0 A1)
  (a0 : El1 A0) (a1 : El1 A1) (ae : eq1 A0 A1 a0 a1)
  (b0 : El1 A0) (b1 : El1 A1) (be : eq1 A0 A1 b0 b1)
  : eq0 SProp0 SProp0 (obseq1 A0 a0 b0) (obseq1 A1 a1 b1).
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
  obseq0 A a0 a1 -> obseq0 B (fsts f a0) (fsts f a1).
Proof.
  exact (snds f a0 a1).
Defined.

Definition proof_irr0 (P : El0 SProp0) (p q : P) : obseq0 (emb0 P) (to_set_intro _ p) (to_set_intro _ q).
Proof.
  easy.
Defined.

Definition funext0 (A : U0) (P : El1 (arr1 (emb1 A) U01)) (f g : El0 (pi0 A P)) :
  (forall a, obseq0 (fsts P a) (fsts f a) (fsts g a)) -> obseq0 (pi0 A P) f g.
Proof.
  intro H. intros a0 a1 ae.
  exact (trans0 (fsts P a0) (fsts P a0) (reflU0 _) (fsts P a1) (H a0) (snds g a0 a1 ae)).
Defined.

Definition propext0 (P Q : El0 SProp0) : sand (P -> Q) (Q -> P) -> obseq0 SProp0 P Q.
Proof.
  intros [H1 H2]. split ; easy.
Defined.

(* NB : a J eliminator can be derived from cast + ap + UIP
   However, the computation rule for J on reflexivity is weakened to a propositional equality.

   If we use Impredicative-Set instead of SProp, then we can use a Swan-style encoding to define
   an observational equality with definitional J-on-refl *)

(* Quotient types à la Hofmann *)

Definition quotient0 (A : U0) (R : El0 (arr0 A (arr0 A SProp0))) : U0.
Proof.
  refine (Quo0 A (fun a b => fsts (fsts R a) b) (snds R)).
Defined.

Definition quotient0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 SProp0))) (R1 : El0 (arr0 A1 (arr0 A1 SProp0)))
  (Re : eq0 (arr0 A0 (arr0 A0 SProp0)) (arr0 A1 (arr0 A1 SProp0)) R0 R1) :
  eq1 U01 U01 (quotient0 A0 R0) (quotient0 A1 R1).
Proof.
  split.
  - exact Ae.
  - exact Re.
Defined.

Definition quo_in0 (A : U0) (R : El0 (arr0 A (arr0 A SProp0))) (a : El0 A) : El0 (quotient0 A R).
Proof.
  exact a.
Defined.

Definition quo_in0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 SProp0))) (R1 : El0 (arr0 A1 (arr0 A1 SProp0)))
  (Re : eq0 (arr0 A0 (arr0 A0 SProp0)) (arr0 A1 (arr0 A1 SProp0)) R0 R1)
  (a0 : El0 A0) (a1 : El0 A1) (ae : eq0 A0 A1 a0 a1)
  : eq0 (quotient0 A0 R0) (quotient0 A1 R1) (quo_in0 A0 R0 a0) (quo_in0 A1 R1 a1).
Proof.
  exists a0. exists a1. split.
  - eapply clo_refl. eapply refl0.
  - split. exact ae. eapply clo_refl. eapply refl0.
Defined.

Definition quo_eq (A : U0) (R : El0 (arr0 A (arr0 A SProp0)))
  (a b : El0 A) (e : fsts (fsts R a) b) :
  eq0 (quotient0 A R) (quotient0 A R) (quo_in0 A R a) (quo_in0 A R b).
Proof.
  exists b. exists b. split.
  - eapply clo_emb. exact e.
  - split. eapply refl0. eapply clo_refl. eapply refl0.
Defined.

Definition quo_rec0 (A : U0) (R : El0 (arr0 A (arr0 A SProp0))) (P : El1 (arr1 (emb1 (quotient0 A R)) U01))
  (Pq : El0 (pi0 A
               (lam1 (emb1 A) U01
                  (fun a => (app1 P (quo_in0 A R a)))
                  (fun a b e => (app1e (reflU1 (emb1 (quotient0 A R))) (reflU1 U01) (refl1 _ P)
                                   (quo_in0e A A (reflU0 A) R R (refl0 _ R) a b e))))))
  (Peq : forall (a b : El0 A) (rab : fsts (fsts R a) b), eq0 (fsts P (quo_in0 A R a)) (fsts P (quo_in0 A R b)) (fsts Pq a) (fsts Pq b))
  (x : El0 (quotient0 A R)) : El0 (app1 P x).
Proof.
  exact (fsts Pq x).
Defined.

Definition quo_rec0e (A0 A1 : U0) (Ae : eqU0 A0 A1)
  (R0 : El0 (arr0 A0 (arr0 A0 SProp0))) (R1 : El0 (arr0 A1 (arr0 A1 SProp0)))
  (Re : eq0 (arr0 A0 (arr0 A0 SProp0)) (arr0 A1 (arr0 A1 SProp0)) R0 R1)
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
  (Peq0 : forall (a b : El0 A0) (rab : fsts (fsts R0 a) b), eq0 (fsts P0 (quo_in0 A0 R0 a)) (fsts P0 (quo_in0 A0 R0 b)) (fsts Pq0 a) (fsts Pq0 b))
  (Peq1 : forall (a b : El0 A1) (rab : fsts (fsts R1 a) b), eq0 (fsts P1 (quo_in0 A1 R1 a)) (fsts P1 (quo_in0 A1 R1 b)) (fsts Pq1 a) (fsts Pq1 b))
  (x0 : El0 (quotient0 A0 R0)) (x1 : El0 (quotient0 A1 R1)) (xe : eq0 (quotient0 A0 R0) (quotient0 A1 R1) x0 x1)
  : eq0 (app1 P0 x0) (app1 P1 x1) (quo_rec0 A0 R0 P0 Pq0 Peq0 x0) (quo_rec0 A1 R1 P1 Pq1 Peq1 x1).
Proof.
  change (eq0 (app1 P0 x0) (app1 P1 x1) (fsts Pq0 x0) (fsts Pq1 x1)).
  destruct xe as [y0 [y1 [e0 [ey e1]]]].
  assert (eqU0 (app1 P0 x0) (app1 P0 y0)) as eP0.
  { refine (snds P0 x0 y0 _). exists y0. exists y0. split.
    exact e0. split. eapply refl0. eapply clo_refl. eapply refl0. }
  assert (eq0 (app1 P0 x0) (app1 P0 y0) (fsts Pq0 x0) (fsts Pq0 y0)) as ePxy0.
  { clear Pq1 Pqe Peq1 x1 y1 ey e1 eP0. induction e0.
    - eapply Peq0. exact r.
    - exact (snds Pq0 a b e).
    - eapply sym0. exact IHe0.
    - unshelve refine (trans0 (app1 P0 a) (app1 P0 b) _ (app1 P0 c) IHe0_1 IHe0_2).
      refine (snds P0 a b _). exists b. exists b. split.
      exact e0_1. split. eapply refl0. eapply clo_refl. eapply refl0. }
  assert (eq0 (app1 P0 y0) (app1 P1 y1) (fsts Pq0 y0) (fsts Pq1 y1)) as ePy.
  { exact (Pqe y0 y1 ey). }
  assert (eqU0 (app1 P1 y1) (app1 P1 x1)) as eP1.
  { refine (snds P1 y1 x1 _). exists x1. exists x1. split.
    exact e1. split. eapply refl0. eapply clo_refl. eapply refl0. }
  assert (eq0 (app1 P1 y1) (app1 P1 x1) (fsts Pq1 y1) (fsts Pq1 x1)) as ePxy1.
  { clear Pq0 Pqe Peq0 x0 y0 ey e0 eP0 eP1 ePxy0 ePy. induction e1.
    - eapply Peq1. exact r.
    - exact (snds Pq1 a b e).
    - eapply sym0. exact IHe1.
    - unshelve refine (trans0 (app1 P1 a) (app1 P1 b) _ (app1 P1 c) IHe1_1 IHe1_2).
      refine (snds P1 a b _). exists b. exists b. split.
      exact e1_1. split. eapply refl0. eapply clo_refl. eapply refl0. }
  refine (trans0 (app1 P0 x0) (app1 P0 y0) eP0 (app1 P1 x1) ePxy0 _).
  eapply sym0. apply sym0 in ePxy1. apply sym0 in ePy.
  refine (trans0 (app1 P1 x1) (app1 P1 y1) (symU0 _ _ eP1) (app1 P0 y0) ePxy1 ePy).
Defined.
