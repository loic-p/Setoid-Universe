(* ************************************* *)
(* A Universe for Proof-Relevant Setoids *)
(* ************************************* *)

(* This file contains the definition of our setoid model as a CwF *)

Set Universe Polymorphism.
Set Primitive Projections.
Require Import utils.
Require Import univ0 univ0_lemmas.
Require Import univ1 univ1_lemmas.

(* We define our model as a CwF. The type of contexts is U1. *)

Definition Con := U1.

Definition arr1 (A B : U1) : U1 := Pi1 A (fun _ => B) (fun _ _ _ => reflU1 B).
Definition Sub (Δ Γ : Con) := El1 (arr1 Δ Γ).

(* Identity substitution *)

Definition idSub (Γ : Con) : Sub Γ Γ.
Proof.
  unshelve econstructor.
  - exact (fun x => x).
  - intros. exact ae.
Defined.

(* Substitution composition *)

Definition compSub {Γ Δ Ξ : Con} (σ : Sub Δ Γ) (τ : Sub Ξ Δ) : Sub Ξ Γ.
Proof.
  unshelve econstructor.
  - exact (fun x => fsts σ (fsts τ x)).
  - intros. refine (snds σ (fsts τ a0) (fsts τ a1) _).
    exact (snds τ a0 a1 ae).
Defined.
Notation "σ ∘ τ" := (compSub σ τ) (at level 60, right associativity).

(* Composition is definitionally associative and unital *)

Lemma compAssoc {Γ Δ Ξ Ξ' : Con} (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (τ' : Sub Ξ' Ξ) : (σ ∘ τ) ∘ τ' = σ ∘ (τ ∘ τ').
Proof.
  reflexivity.
Qed.

Lemma compIdLeft {Γ Δ : Con} (σ : Sub Δ Γ) : (idSub Γ) ∘ σ = σ.
Proof.
  reflexivity.
Qed.

Lemma compIdRight {Γ Δ : Con} (σ : Sub Δ Γ) : σ ∘ (idSub Δ) = σ.
Proof.
  reflexivity.
Qed.

(* Large types *)

Definition TY (Γ : Con) := Sigmas (El1 Γ -> U1) (fun f => forall (γ0 γ1 : El1 Γ) (γe : eq1 Γ Γ γ0 γ1), eqU1 (f γ0) (f γ1)).

(* Substitution/reindexing of types *)

Definition tySubst {Γ Δ : Con} (A : TY Γ) (σ : Sub Δ Γ) : TY Δ.
Proof.
  unshelve econstructor.
  - exact (fun δ => fsts A (fsts σ δ)).
  - exact (fun δ0 δ1 δe => snds A (fsts σ δ0) (fsts σ δ1) (snds σ δ0 δ1 δe)).
Defined.

Notation "A [ σ ]T" := (tySubst A σ) (at level 30).

(* Substitution is definitionally functorial *)

Lemma substId {Γ : Con} (A : TY Γ) : A [ idSub Γ ]T = A.
Proof.
  reflexivity.
Qed.

Lemma substComp {Γ Δ Ξ : Con} (A : TY Γ) (σ : Sub Δ Γ) (τ : Sub Ξ Δ) : A [ σ ∘ τ ]T = A [ σ ]T [ τ ]T.
Proof.
  reflexivity.
Qed.

(* Terms *)

Definition TM (Γ : Con) (A : TY Γ) := El1 (Pi1 Γ (fun γ => fsts A γ) (snds A)).

(* Substitution/reindexing of terms *)

Definition tmSubst {Γ Δ : Con} {A : TY Γ} (t : TM Γ A) (σ : Sub Δ Γ) : TM Δ (A [σ]T).
Proof.
  unshelve econstructor.
  - exact (fun δ => fsts t (fsts σ δ)).
  - refine (fun δ0 δ1 δe => snds t (fsts σ δ0) (fsts σ δ1) (snds σ δ0 δ1 δe)).
Defined.

Notation "a [ σ ]t" := (tmSubst a σ) (at level 30).

(* Substitution is definitionally functorial *)

Lemma substIdTm {Γ : Con} (A : TY Γ) (a : TM Γ A) : a [ idSub Γ ]t = a.
Proof.
  reflexivity.
Qed.

Lemma substCompTm {Γ Δ Ξ : Con} (A : TY Γ) (a : TM Γ A) (σ : Sub Δ Γ) (τ : Sub Ξ Δ) : a [ σ ∘ τ ]t = a [ σ ]t [ τ ]t.
Proof.
  reflexivity.
Qed.

(* Context extension with weakening, variable (p and q in CwF notations) and substitution extension *)

Definition ConExt (Γ : Con) (A : TY Γ) : Con := Sigma1 Γ (fun γ => fsts A γ) (snds A).

Notation "Γ ▹ A" := (ConExt Γ A) (at level 50, left associativity).

Definition Wk {Γ : Con} (A : TY Γ) : Sub (Γ ▹ A) Γ.
Proof.
  unshelve econstructor.
  - exact (fun x => fst x).
  - exact (fun x0 x1 xe => andleft xe).
Defined.

Definition Var0 {Γ : Con} (A : TY Γ) : TM (Γ ▹ A) (A [Wk A]T).
Proof.
  unshelve econstructor.
  - exact (fun x => snd x).
  - exact (fun x0 x1 xe => andright xe).
Defined.

Definition subExt {Γ Δ : Con} (A : TY Γ) (σ : Sub Δ Γ) (a : TM Δ (A [σ]T)) : Sub Δ (Γ ▹ A).
Proof.
  unshelve econstructor.
  - exact (fun δ => mkPair (fsts σ δ) (fsts a δ)).
  - refine (fun δ0 δ1 δe => mkAndEx (snds σ δ0 δ1 δe) (snds a δ0 δ1 δe)).
Defined.

Notation "⟨ σ , a ⟩" := (subExt _ σ a).

(* β and η laws for substitutions are definitional *)

Lemma subExtβ1 {Γ Δ : Con} (A : TY Γ) (σ : Sub Δ Γ) (a : TM Δ (A [σ]T)) : (Wk A) ∘ ⟨ σ , a ⟩ = σ.
Proof.
  reflexivity.
Qed.

Lemma subExtβ2 {Γ Δ : Con} (A : TY Γ) (σ : Sub Δ Γ) (a : TM Δ (A [σ]T)) : (Var0 A)[⟨ σ , a ⟩]t = a.
Proof.
  reflexivity.
Qed.

Lemma subExtη {Γ Δ : Con} (A : TY Γ) (σ : Sub Δ (Γ ▹ A)) : σ = ⟨ (Wk A) ∘ σ , (Var0 A)[σ]t ⟩.
Proof.
  reflexivity.
Qed.

(* Thus we have a CwF in which all the equations are definitional.
   Now it remains to show that this CwF supports all the type formers of MLTT. *)

(* But first, some utilities for substitutions *)

Definition Lift {Γ Δ : Con} (σ : Sub Δ Γ) (A : TY Γ) : Sub (Δ ▹ A [σ]T) (Γ ▹ A).
Proof.
  unshelve econstructor.
  - exact (fun x => mkPair (fsts σ (fst x)) (snd x)).
  - unshelve refine (fun x0 x1 xe => mkAndEx (snds σ (fst x0) (fst x1) (andleft xe)) (andright xe)).
Defined.

Definition SgSub {Γ : Con} {A : TY Γ} (t : TM Γ A) : Sub Γ (Γ ▹ A) := ⟨ idSub Γ , t ⟩.

(* Dependent products of large types *)

Definition ΠΠ {Γ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) : TY Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => Pi1 (fsts A γ) (fun a => fsts B (mkPair γ a))
                        (fun a0 a1 ae => snds B (mkPair γ a0) (mkPair γ a1) (mkAndEx (refl1 Γ γ) ae))).
  - exact (fun γ0 γ1 γe => sand_intro (snds A γ0 γ1 γe)
                                      (fun a0 a1 ae => snds B (mkPair γ0 a0) (mkPair γ1 a1) (mkAndEx γe ae))).
Defined.

Lemma substΠΠ {Γ Δ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) (σ : Sub Δ Γ) : (ΠΠ A B) [σ]T = ΠΠ (A [σ]T) (B [Lift σ A]T).
Proof.
  reflexivity.
Qed.

(* Lambda abstraction *)

Definition LAM {Γ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) (t : TM (Γ ▹ A) B) : TM Γ (ΠΠ A B).
Proof.
  unshelve econstructor.
  - intro γ. unshelve econstructor.
    + exact (fun a => fsts t (mkPair γ a)).
    + unshelve refine (fun a0 a1 ae => snds t (mkPair γ a0) (mkPair γ a1) (mkAndEx (refl1 Γ γ) ae)).
  - exact (fun γ0 γ1 γe a0 a1 ae => snds t (mkPair γ0 a0) (mkPair γ1 a1) (mkAndEx γe ae)).
Defined.

Lemma substLAM {Γ Δ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) (t : TM (Γ ▹ A) B) (σ : Sub Δ Γ) :
  (LAM A B t) [σ]t = LAM (A [σ]T) (B [Lift σ A]T) (t [Lift σ A]t).
Proof.
  reflexivity.
Qed.

(* Function application *)

Definition APP {Γ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) (t : TM Γ (ΠΠ A B)) (u : TM Γ A) : TM Γ (B [SgSub u]T).
Proof.
  unshelve econstructor.
  - exact (fun γ => fsts (fsts t γ) (fsts u γ)).
  - exact (fun γ0 γ1 γe => snds t γ0 γ1 γe (fsts u γ0) (fsts u γ1) (snds u γ0 γ1 γe)).
Defined.

Lemma substAPP {Γ Δ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) (t : TM Γ (ΠΠ A B)) (u : TM Γ A) (σ : Sub Δ Γ) :
  (APP A B t u) [σ]t = APP (A [σ]T) (B [Lift σ A]T) (t [σ]t) (u [σ]t).
Proof.
  reflexivity.
Qed.

(* β and η laws for functions are definitional *)

Lemma ΠΠβ {Γ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) (t : TM (Γ ▹ A) B) (u : TM Γ A) : APP A B (LAM A B t) u = t [SgSub u]t.
Proof.
  reflexivity.
Qed.

Lemma ΠΠη {Γ : Con} (A : TY Γ) (B : TY (Γ ▹ A)) (t : TM Γ (ΠΠ A B)) : t = LAM A B (APP (A [Wk A]T) (B [Lift (Wk A) A]T) (t [Wk A]t) (Var0 A)).
Proof.
  reflexivity.
Qed.

(* Nondependent functions between large types *)

Definition ARR {Γ : Con} (A : TY Γ) (B : TY Γ) : TY Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => Pi1 (fsts A γ) (fun _ => fsts B γ)
                        (fun _ _ _ => reflU1 (fsts B γ))).
  - exact (fun γ0 γ1 γe => sand_intro (snds A γ0 γ1 γe)
                                      (fun _ _ _ => snds B γ0 γ1 γe)).
Defined.

Lemma substARR {Γ Δ : Con} (A : TY Γ) (B : TY Γ) (σ : Sub Δ Γ) : (ARR A B) [σ]T = ARR (A [σ]T) (B [σ]T).
Proof.
  reflexivity.
Qed.

Definition APP' {Γ : Con} (A : TY Γ) (B : TY Γ) (t : TM Γ (ARR A B)) (u : TM Γ A) : TM Γ B.
Proof.
  unshelve econstructor.
  - exact (fun γ => fsts (fsts t γ) (fsts u γ)).
  - exact (fun γ0 γ1 γe => snds t γ0 γ1 γe (fsts u γ0) (fsts u γ1) (snds u γ0 γ1 γe)).
Defined.

Lemma substAPP' {Γ Δ : Con} (A : TY Γ) (B : TY Γ) (t : TM Γ (ARR A B)) (u : TM Γ A) (σ : Sub Δ Γ) :
  (APP' A B t u) [σ]t = APP' (A [σ]T) (B [σ]T) (t [σ]t) (u [σ]t).
Proof.
  reflexivity.
Qed.

(* Universe of small types *)

Definition U (Γ : Con) : TY Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => U01).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substU (Γ Δ : Con) (σ : Sub Δ Γ) : (U Γ) [σ]T = U Δ.
Proof.
  reflexivity.
Qed.

Definition Ty (Γ : Con) := TM Γ (U Γ).

Definition El {Γ : Con} (A : Ty Γ) : TY Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => emb1 (fsts A γ)).
  - exact (snds A).
Defined.

Lemma substEl {Γ Δ : Con} (A : Ty Γ) (σ : Sub Δ Γ) : (El A) [σ]T = El (A [σ]t).
Proof.
  reflexivity.
Qed.

Definition Tm (Γ : Con) (A : Ty Γ) := TM Γ (El A).

(* Some utilities *)

Definition conExt (Γ : Con) (A : Ty Γ) : Con := Γ ▹ (El A).

Notation "Γ ▸ A" := (conExt Γ A) (at level 50, left associativity).

Definition lift {Γ Δ : Con} (σ : Sub Δ Γ) (A : Ty Γ) : Sub (Δ ▸ A [σ]t) (Γ ▸ A) := Lift σ (El A).

Definition wk {Γ : Con} (A : Ty Γ) : Sub (Γ ▸ A) Γ := Wk (El A).

Definition var0 {Γ : Con} (A : Ty Γ) : Tm (Γ ▸ A) (A [wk A]t) := Var0 (El A).

Definition sgSub {Γ : Con} {A : Ty Γ} (t : Tm Γ A) : Sub Γ (Γ ▸ A) := subExt (El A) (idSub Γ) t.

(* Dependent products of small types.
   Note that El (Π A B) ≠ ΠΠ (El A) (El B). We could probably enforce that equality if we used a recursive embedding... *)

Definition Π {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) : Ty Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => Pi0 (fsts A γ) (fun a => fsts B (mkPair γ a))
                        (fun a0 a1 ae => snds B (mkPair γ a0) (mkPair γ a1) (mkAndEx (refl1 Γ γ) ae))).
  - exact (fun γ0 γ1 γe => sand_intro (snds A γ0 γ1 γe)
                                      (fun a0 a1 ae => snds B (mkPair γ0 a0) (mkPair γ1 a1) (mkAndEx γe ae))).
Defined.

Lemma substΠ {Γ Δ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (σ : Sub Δ Γ) : (Π A B) [σ]t = Π (A [σ]t) (B [lift σ A]t).
Proof.
  reflexivity.
Qed.

(* Lambda abstraction *)

Definition lam {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm (Γ ▸ A) B) : Tm Γ (Π A B).
Proof.
  unshelve econstructor.
  - intro γ. unshelve econstructor.
    + exact (fun a => fsts t (mkPair γ a)).
    + unshelve refine (fun a0 a1 ae => snds t (mkPair γ a0) (mkPair γ a1) (mkAndEx (refl1 Γ γ) ae)).
  - exact (fun γ0 γ1 γe a0 a1 ae => snds t (mkPair γ0 a0) (mkPair γ1 a1) (mkAndEx γe ae)).
Defined.

Lemma substLam {Γ Δ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm (Γ ▸ A) B) (σ : Sub Δ Γ) :
  (lam A B t) [σ]t = lam (A [σ]t) (B [lift σ A]t) (t [lift σ A]t).
Proof.
  reflexivity.
Qed.

(* Function application *)

Definition app {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Π A B)) (u : Tm Γ A) : Tm Γ (B [sgSub u]t).
Proof.
  unshelve econstructor.
  - exact (fun γ => fsts (fsts t γ) (fsts u γ)).
  - exact (fun γ0 γ1 γe => snds t γ0 γ1 γe (fsts u γ0) (fsts u γ1) (snds u γ0 γ1 γe)).
Defined.

Lemma substApp {Γ Δ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Π A B)) (u : Tm Γ A) (σ : Sub Δ Γ) :
  (app A B t u) [σ]t = app (A [σ]t) (B [lift σ A]t) (t [σ]t) (u [σ]t).
Proof.
  reflexivity.
Qed.

(* β and η laws for functions are definitional *)

Lemma Πβ {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm (Γ ▸ A) B) (u : Tm Γ A) : app A B (lam A B t) u = t [sgSub u]t.
Proof.
  reflexivity.
Qed.

Lemma Πη {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Π A B)) : t = lam A B (app (A [wk A]t) (B [lift (wk A) A]t) (t [wk A]t) (var0 A)).
Proof.
  reflexivity.
Qed.

(* Σ-types *)

Definition Σ {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) : Ty Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => Sigma0 (fsts A γ) (fun a => fsts B (mkPair γ a))
                           (fun a0 a1 ae => snds B (mkPair γ a0) (mkPair γ a1) (mkAndEx (refl1 Γ γ) ae))).
  - exact (fun γ0 γ1 γe => sand_intro (snds A γ0 γ1 γe)
                                      (fun a0 a1 ae => snds B (mkPair γ0 a0) (mkPair γ1 a1) (mkAndEx γe ae))).
Defined.

Lemma substΣ {Γ Δ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (σ : Sub Δ Γ) : (Σ A B) [σ]t = Σ (A [σ]t) (B [lift σ A]t).
Proof.
  reflexivity.
Qed.

(* Pair constructor *)

Definition pair {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ A) (u : Tm Γ (B [sgSub t]t)) : Tm Γ (Σ A B).
Proof.
  unshelve econstructor.
  - intro γ. unshelve refine (mkPair _ _). exact (fsts t γ). exact (fsts u γ). (* weird universe inconsistency if I give the term directly *)
  - intros γ0 γ1 γe. unshelve refine (mkAndEx (snds t γ0 γ1 γe) (snds u γ0 γ1 γe)).
Defined.

Lemma substPair {Γ Δ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ A) (u : Tm Γ (B [sgSub t]t)) (σ : Sub Δ Γ) :
  (pair A B t u) [σ]t = pair (A [σ]t) (B [lift σ A]t) (t [σ]t) (u [σ]t).
Proof.
  reflexivity.
Qed.

(* First projection *)

Definition proj1 {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Σ A B)) : Tm Γ A.
Proof.
  unshelve econstructor.
  - exact (fun γ => fst (fsts t γ)).
  - exact (fun γ0 γ1 γe => andleft (snds t γ0 γ1 γe)).
Defined.

Lemma substProj1 {Γ Δ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Σ A B)) (σ : Sub Δ Γ) :
  (proj1 A B t) [σ]t = proj1 (A [σ]t) (B [lift σ A]t) (t [σ]t).
Proof.
  reflexivity.
Qed.

(* Second projection *)

Definition proj2 {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Σ A B)) : Tm Γ (B [sgSub (proj1 A B t)]t).
Proof.
  unshelve econstructor.
  - exact (fun γ => snd (fsts t γ)).
  - exact (fun γ0 γ1 γe => andright (snds t γ0 γ1 γe)).
Defined.

Lemma substProj2 {Γ Δ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Σ A B)) (σ : Sub Δ Γ) :
  (proj2 A B t) [σ]t = proj2 (A [σ]t) (B [lift σ A]t) (t [σ]t).
Proof.
  reflexivity.
Qed.

(* β and η laws for pairs are definitional *)

Lemma Σβ1 {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ A) (u : Tm Γ (B [sgSub t]t)) :
  proj1 A B (pair A B t u) = t.
Proof.
  reflexivity.
Qed.

Lemma Σβ2 {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ A) (u : Tm Γ (B [sgSub t]t)) :
  proj2 A B (pair A B t u) = u.
Proof.
  reflexivity.
Qed.

Lemma Ση {Γ : Con} (A : Ty Γ) (B : Ty (Γ ▸ A)) (t : Tm Γ (Σ A B)) :
  t = pair A B (proj1 A B t) (proj2 A B t).
Proof.
  reflexivity.
Qed.

(* Natural numbers *)

Definition ℕ (Γ : Con) : Ty Γ.
Proof.
  unshelve econstructor.
  - exact (fun _ => nat0).
  - exact (fun _ _ _ => stt).
Defined.

Lemma substℕ {Γ Δ : Con} (σ : Sub Δ Γ) : (ℕ Γ) [σ]t = ℕ Δ.
Proof.
  reflexivity.
Qed.

(* zero *)

Definition ℕz (Γ : Con) : Tm Γ (ℕ Γ).
Proof.
  unshelve econstructor.
  - exact (fun _ => zero).
  - exact (fun _ _ _ => eqzero).
Defined.

Lemma substℕz {Γ Δ : Con} (σ : Sub Δ Γ) : (ℕz Γ) [σ]t = ℕz Δ.
Proof.
  reflexivity.
Qed.

(* successor *)

Definition ℕS (Γ : Con) (n : Tm Γ (ℕ Γ)) : Tm Γ (ℕ Γ).
Proof.
  unshelve econstructor.
  - exact (fun γ => suc (fsts n γ)).
  - exact (fun γ0 γ1 γe => eqsuc (fsts n γ0) (fsts n γ1) (snds n γ0 γ1 γe)).
Defined.

Lemma substℕS {Γ Δ : Con} (n : Tm Γ (ℕ Γ)) (σ : Sub Δ Γ) : (ℕS Γ n) [σ]t = ℕS Δ (n [σ]t).
Proof.
  reflexivity.
Qed.

(* eliminator *)

Definition ℕrec (Γ : Con) (P : TY (Γ ▸ (ℕ Γ))) (pZ : TM Γ (P [sgSub (ℕz Γ)]T))
  (pS : TM (Γ ▸ (ℕ Γ)) (ARR P (P [(subExt (El (ℕ Γ)) (wk (ℕ Γ)) (ℕS (Γ ▸ (ℕ Γ)) (var0 (ℕ Γ))))]T)))
  (n : Tm Γ (ℕ Γ)) : TM Γ (P [sgSub n]T).
Proof.
  unshelve econstructor.
  - intro γ. refine (nat_rect (fun n => El1 (fsts P (mkPair γ n))) _ _ (fsts n γ)).
    + exact (fsts pZ γ).
    + intros m IH. exact (fsts (fsts pS (mkPair γ m)) IH).
  - intros γ0 γ1 γe.
    refine (nateq_sind (fun n0 n1 ne => eq1 _ _
        (nat_rect (fun n => El1 (fsts P (mkPair γ0 n))) (fsts pZ γ0) (fun m IH => fsts (fsts pS (mkPair γ0 m)) IH) n0)
        (nat_rect (fun n => El1 (fsts P (mkPair γ1 n))) (fsts pZ γ1) (fun m IH => fsts (fsts pS (mkPair γ1 m)) IH) n1))
      _ _ (fsts n γ0) (fsts n γ1) (snds n γ0 γ1 γe)).
    + exact (snds pZ γ0 γ1 γe).
    + intros m0 m1 me IH. refine (snds pS (mkPair γ0 m0) (mkPair γ1 m1) (mkAndEx γe me) _ _ IH).
Defined.

Lemma substℕrec (Γ Δ : Con) (P : TY (Γ ▸ (ℕ Γ))) (pZ : TM Γ (P [sgSub (ℕz Γ)]T))
  (pS : TM (Γ ▸ (ℕ Γ)) (ARR P (P [(subExt (El (ℕ Γ)) (wk (ℕ Γ)) (ℕS (Γ ▸ (ℕ Γ)) (var0 (ℕ Γ))))]T)))
  (n : Tm Γ (ℕ Γ)) (σ : Sub Δ Γ) :
  (ℕrec Γ P pZ pS n) [σ]t = ℕrec Δ (P [lift σ (ℕ Γ)]T) (pZ [σ]t) (pS [lift σ (ℕ Γ)]t) (n [σ]t).
Proof.
  reflexivity.
Qed.

(* β laws for natural numbers are definitional *)

Lemma ℕβ1 (Γ : Con) (P : TY (Γ ▸ (ℕ Γ))) (pZ : TM Γ (P [sgSub (ℕz Γ)]T))
  (pS : TM (Γ ▸ (ℕ Γ)) (ARR P (P [(subExt (El (ℕ Γ)) (wk (ℕ Γ)) (ℕS (Γ ▸ (ℕ Γ)) (var0 (ℕ Γ))))]T))) :
  ℕrec Γ P pZ pS (ℕz Γ) = pZ.
Proof.
  reflexivity.
Qed.

Lemma ℕβ2 (Γ : Con) (P : TY (Γ ▸ (ℕ Γ))) (pZ : TM Γ (P [sgSub (ℕz Γ)]T))
  (pS : TM (Γ ▸ (ℕ Γ)) (ARR P (P [(subExt (El (ℕ Γ)) (wk (ℕ Γ)) (ℕS (Γ ▸ (ℕ Γ)) (var0 (ℕ Γ))))]T))) (n : Tm Γ (ℕ Γ)) :
  ℕrec Γ P pZ pS (ℕS Γ n) = APP' (P [sgSub n]T) (P [sgSub (ℕS Γ n)]T) (pS [sgSub n]t) (ℕrec Γ P pZ pS n).
Proof.
  reflexivity.
Qed.

(* Universe of propositions *)

Definition Ω (Γ : Con) : Ty Γ.
Proof.
  unshelve econstructor.
  - exact (fun _ => SProp0).
  - exact (fun _ _ _ => stt).
Defined.

Lemma substΩ {Γ Δ : Con} (σ : Sub Δ Γ) : (Ω Γ) [σ]t = Ω Δ.
Proof.
  reflexivity.
Qed.

(* Type of elements of a proposition *)

Definition Prf {Γ : Con} (P : Tm Γ (Ω Γ)) : Ty Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => emb0 (fsts P γ)).
  - exact (snds P).
Defined.

Lemma substPrf {Γ Δ : Con} (P : Tm Γ (Ω Γ)) (σ : Sub Δ Γ) : (Prf P) [σ]t = Prf (P [σ]t).
Proof.
  reflexivity.
Qed.

(* Propositions SHOULD satisfy definitional proof irrelevance. However, that requires η for the embedding of SProp into Type
   (for instance, a record with one SProp field would do the trick, but these do not support η in Rocq at the moment) *)

Lemma prfIrr {Γ : Con} (P : Tm Γ (Ω Γ)) (p q : Tm Γ (Prf P)) : p = q.
Proof.
  Fail reflexivity.
Abort.

(* False proposition *)

Definition false (Γ : Con) : Tm Γ (Ω Γ).
Proof.
  unshelve econstructor.
  - exact (fun γ => sFalse).
  - exact (fun γ0 γ1 γe => sand_intro (fun x => x) (fun x => x)).
Defined.

Lemma substFalse {Γ Δ : Con} (σ : Sub Δ Γ) : (false Γ) [σ]t = false Δ.
Proof.
  reflexivity.
Qed.

(* Large elimination of False *)

Definition efq {Γ : Con} (A : TY Γ) (abs : Tm Γ (Prf (false Γ))) : TM Γ A.
Proof.
  unshelve econstructor.
  - exact (fun γ => sFalse_rect (fun _ => El1 (fsts A γ)) (to_set_esc sFalse (fsts abs γ))).
  - refine (fun γ0 γ1 γe => _). destruct (fsts abs γ0). destruct a.
Defined.

Lemma substEfq {Γ Δ : Con} (A : TY Γ) (abs : Tm Γ (Prf (false Γ))) (σ : Sub Δ Γ) :
  (efq A abs) [σ]t = efq (A [σ]T) (abs[σ]t).
Proof.
  reflexivity.
Qed.

(* Impredicative quantification *)

Definition for_all {Γ : Con} (A : Ty Γ) (P : Tm (Γ ▸ A) (Ω (Γ ▸ A))) : Tm Γ (Ω Γ).
Proof.
  unshelve econstructor.
  - exact (fun γ => forall (a : El0 (fsts A γ)), fsts P (mkPair γ a)).
  - intros γ0 γ1 γe. econstructor.
    + intros H a1. set (a0 := cast0 (fsts A γ1) (fsts A γ0) (symU0 _ _ (snds A γ0 γ1 γe)) a1).
      pose proof (cast0_eq (fsts A γ1) (fsts A γ0) (symU0 _ _ (snds A γ0 γ1 γe)) a1) as ae. change (eq0 _ _ a1 a0) in ae.
      pose proof (snds P (mkPair γ0 a0) (mkPair γ1 a1) (mkAndEx γe (sym0 _ _ ae))) as Pe.
      change (sand ((fsts P (mkPair γ0 a0)) -> (fsts P (mkPair γ1 a1))) ((fsts P (mkPair γ1 a1)) -> (fsts P (mkPair γ0 a0)))) in Pe.
      exact (sand_fst Pe (H a0)).
    + intros H a0. set (a1 := cast0 (fsts A γ0) (fsts A γ1) (snds A γ0 γ1 γe) a0).
      pose proof (cast0_eq (fsts A γ0) (fsts A γ1) (snds A γ0 γ1 γe) a0) as ae. change (eq0 _ _ a0 a1) in ae.
      pose proof (snds P (mkPair γ0 a0) (mkPair γ1 a1) (mkAndEx γe ae)) as Pe.
      change (sand ((fsts P (mkPair γ0 a0)) -> (fsts P (mkPair γ1 a1))) ((fsts P (mkPair γ1 a1)) -> (fsts P (mkPair γ0 a0)))) in Pe.
      exact (sand_snd Pe (H a1)).
Defined.

Lemma substForall {Γ Δ : Con} (A : Ty Γ) (P : Tm (Γ ▸ A) (Ω (Γ ▸ A))) (σ : Sub Δ Γ) :
  (for_all A P) [σ]t = for_all (A [σ]t) (P [lift σ A]t).
Proof.
  reflexivity.
Qed.

(* Introduction for impredicative forall *)

Definition forall_lam {Γ : Con} (A : Ty Γ) (P : Tm (Γ ▸ A) (Ω (Γ ▸ A))) (t : Tm (Γ ▸ A) (Prf P)) : Tm Γ (Prf (for_all A P)).
Proof.
  unshelve econstructor.
  - exact (fun γ => to_set_intro (fsts (for_all A P) γ) (fun a => to_set_esc _ (fsts t (mkPair γ a)))).
  - intros γ0 γ1 γe. exact stt.
Defined.

Lemma substForall_lam {Γ Δ : Con} (A : Ty Γ) (P : Tm (Γ ▸ A) (Ω (Γ ▸ A))) (t : Tm (Γ ▸ A) (Prf P)) (σ : Sub Δ Γ) :
  (forall_lam A P t) [σ]t = forall_lam (A [σ]t) (P [lift σ A]t) (t [lift σ A]t).
Proof.
  reflexivity.
Qed.

(* Elimination for impredicative forall *)

Definition forall_app {Γ : Con} (A : Ty Γ) (P : Tm (Γ ▸ A) (Ω (Γ ▸ A))) (t : Tm Γ (Prf (for_all A P))) (u : Tm Γ A) :
  Tm Γ (Prf (P [sgSub u]t)).
Proof.
  unshelve econstructor.
  - refine (fun γ => to_set_intro _ (to_set_esc _ (fsts t γ) (fsts u γ))).
  - intros γ0 γ1 γe. exact stt.
Defined.

Lemma substForall_app {Γ Δ : Con} (A : Ty Γ) (P : Tm (Γ ▸ A) (Ω (Γ ▸ A))) (t : Tm Γ (Prf (for_all A P))) (u : Tm Γ A) (σ : Sub Δ Γ) :
  (forall_app A P t u) [σ]t = forall_app (A [σ]t) (P [lift σ A]t) (t [σ]t) (u [σ]t).
Proof.
  reflexivity.
Qed.

(* Logical conjunction
   It could alternatively be derived from impredicative forall, but a direct definition is more convenient. *)

Definition conj {Γ : Con} (P Q : Tm Γ (Ω Γ)) : Tm Γ (Ω Γ).
Proof.
  unshelve econstructor.
  - exact (fun γ => sand (fsts P γ) (fsts Q γ)).
  - intros γ0 γ1 γe. constructor.
    + intro H. exact (sand_intro (sand_fst (snds P γ0 γ1 γe) (sand_fst H)) (sand_fst (snds Q γ0 γ1 γe) (sand_snd H))).
    + intro H. exact (sand_intro (sand_snd (snds P γ0 γ1 γe) (sand_fst H)) (sand_snd (snds Q γ0 γ1 γe) (sand_snd H))).
Defined.

Lemma substConj {Γ Δ : Con} (P Q : Tm Γ (Ω Γ)) (σ : Sub Δ Γ) : (conj P Q) [σ]t = conj (P [σ]t) (Q [σ]t).
Proof.
  reflexivity.
Qed.

(* Logical implication
   It could alternatively be derived from impredicative forall, but a direct definition is more convenient. *)

Definition impl {Γ : Con} (P Q : Tm Γ (Ω Γ)) : Tm Γ (Ω Γ).
Proof.
  unshelve econstructor.
  - exact (fun γ => (fsts P γ) -> (fsts Q γ)).
  - intros γ0 γ1 γe. constructor.
    + intros H p. exact (sand_fst (snds Q γ0 γ1 γe) (H (sand_snd (snds P γ0 γ1 γe) p))).
    + intros H p. exact (sand_snd (snds Q γ0 γ1 γe) (H (sand_fst (snds P γ0 γ1 γe) p))).
Defined.

Lemma substImpl {Γ Δ : Con} (P Q : Tm Γ (Ω Γ)) (σ : Sub Δ Γ) : (impl P Q) [σ]t = impl (P [σ]t) (Q [σ]t).
Proof.
  reflexivity.
Qed.

(* Observational equality *)

Definition obseq {Γ : Con} (A : TY Γ) (x y : TM Γ A) : Tm Γ (Ω Γ).
Proof.
  unshelve econstructor.
  - exact (fun γ => eq1 (fsts A γ) (fsts A γ) (fsts x γ) (fsts y γ)).
  - intros γ0 γ1 γe. constructor.
    + intro e0. refine (trans1 (fsts A γ1) (fsts A γ0) (symU1 _ _ (snds A γ0 γ1 γe)) (fsts A γ1) (sym1 _ _ (snds x γ0 γ1 γe)) _).
      refine (trans1 (fsts A γ0) (fsts A γ0) (reflU1 (fsts A γ0)) (fsts A γ1) e0 _).
      exact (snds y γ0 γ1 γe).
    + intro e0. refine (trans1 (fsts A γ0) (fsts A γ1) (snds A γ0 γ1 γe) (fsts A γ0) (snds x γ0 γ1 γe) _).
      refine (trans1 (fsts A γ1) (fsts A γ1) (reflU1 (fsts A γ1)) (fsts A γ0) e0 _).
      exact (sym1 _ _ (snds y γ0 γ1 γe)).
Defined.

Lemma substObseq {Γ Δ : Con} (A : TY Γ) (x y : TM Γ A) (σ : Sub Δ Γ) :
  (obseq A x y) [σ]t = obseq (A [σ]T) (x [σ]t) (y [σ]t).
Proof.
  reflexivity.
Qed.

(* Reflexivity *)

Definition obseq_refl {Γ : Con} (A : TY Γ) (x : TM Γ A) : Tm Γ (Prf (obseq A x x)).
Proof.
  unshelve econstructor.
  - exact (fun γ => to_set_intro _ (refl1 (fsts A γ) (fsts x γ))).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substObseq_refl {Γ Δ : Con} (A : TY Γ) (x : TM Γ A) (σ : Sub Δ Γ) :
  (obseq_refl A x) [σ]t = obseq_refl (A [σ]T) (x [σ]t).
Proof.
  reflexivity.
Qed.

(* Type coercion operator *)

Definition cast {Γ : Con} (A B : Ty Γ) (e : Tm Γ (Prf (obseq (U Γ) A B))) (a : Tm Γ A) : Tm Γ B.
Proof.
  unshelve econstructor.
  - refine (fun γ => cast0 (fsts A γ) (fsts B γ) (to_set_esc _ (fsts e γ)) (fsts a γ)).
  - intros γ0 γ1 γe.
    refine (trans0 (fsts B γ0) (fsts A γ0) (symU0 _ _ (to_set_esc _ (fsts e γ0))) (fsts B γ1)
                   (sym0 _ _ (cast0_eq (fsts A γ0) (fsts B γ0) (to_set_esc _ (fsts e γ0)) (fsts a γ0))) _).
    refine (trans0 (fsts A γ0) (fsts A γ1) (snds A γ0 γ1 γe) (fsts B γ1) (snds a γ0 γ1 γe) _).
    exact (cast0_eq (fsts A γ1) (fsts B γ1) (to_set_esc _ (fsts e γ1)) (fsts a γ1)).
Defined.

Lemma substCast {Γ Δ : Con} (A B : Ty Γ) (e : Tm Γ (Prf (obseq (U Γ) A B))) (a : Tm Γ A) (σ : Sub Δ Γ) :
  (cast A B e a) [σ]t = cast (A [σ]t) (B [σ]t) (e [σ]t) (a [σ]t).
Proof.
  reflexivity.
Qed.

(* Cast on reflexivity *)

Definition castrefl {Γ : Con} (A : Ty Γ) (a : Tm Γ A) : Tm Γ (Prf (obseq (El A) a (cast A A (obseq_refl (U Γ) A) a))).
Proof.
  unshelve econstructor.
  - exact (fun γ => to_set_intro _ (cast0_eq (fsts A γ) (fsts A γ) (reflU0 (fsts A γ)) (fsts a γ))).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substCastrefl {Γ Δ : Con} (A : Ty Γ) (a : Tm Γ A) (σ : Sub Δ Γ) : (castrefl A a) [σ]t = castrefl (A [σ]t) (a [σ]t).
Proof.
  reflexivity.
Qed.

(* Properties of equality: symmetry, transitivity, function congruence *)

Definition sym {Γ : Con} (A : TY Γ) (x y : TM Γ A) (e : Tm Γ (Prf (obseq A x y))) : Tm Γ (Prf (obseq A y x)).
Proof.
  unshelve econstructor.
  - exact (fun γ => to_set_intro _ (sym1 (fsts A γ) (fsts A γ) (to_set_esc _ (fsts e γ)))).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substSym {Γ Δ : Con} (A : TY Γ) (x y : TM Γ A) (e : Tm Γ (Prf (obseq A x y))) (σ : Sub Δ Γ) :
  (sym A x y e) [σ]t = sym (A [σ]T) (x [σ]t) (y [σ]t) (e [σ]t).
Proof.
  reflexivity.
Qed.

Definition trans {Γ : Con} (A : TY Γ) (x y z : TM Γ A) (e1 : Tm Γ (Prf (obseq A x y))) (e2 : Tm Γ (Prf (obseq A y z))) :
  Tm Γ (Prf (obseq A x z)).
Proof.
  unshelve econstructor.
  - exact (fun γ => to_set_intro _ (trans1 (fsts A γ) (fsts A γ) (reflU1 (fsts A γ)) (fsts A γ)
                                           (to_set_esc _ (fsts e1 γ)) (to_set_esc _ (fsts e2 γ)))).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substTrans {Γ Δ : Con} (A : TY Γ) (x y z : TM Γ A) (e1 : Tm Γ (Prf (obseq A x y))) (e2 : Tm Γ (Prf (obseq A y z)))
  (σ : Sub Δ Γ) : (trans A x y z e1 e2) [σ]t = trans (A [σ]T) (x [σ]t) (y [σ]t) (z [σ]t) (e1 [σ]t) (e2 [σ]t).
Proof.
  reflexivity.
Qed.

Definition cong {Γ : Con} (A B : TY Γ) (f : TM Γ (ARR A B)) (x y : TM Γ A) (e : Tm Γ (Prf (obseq A x y))) :
  Tm Γ (Prf (obseq B (APP' A B f x) (APP' A B f y))).
Proof.
  unshelve econstructor.
  - exact (fun γ => to_set_intro _ (snds (fsts f γ) (fsts x γ) (fsts y γ) (to_set_esc _ (fsts e γ)))).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substCong {Γ Δ : Con} (A B : TY Γ) (f : TM Γ (ARR A B)) (x y : TM Γ A) (e : Tm Γ (Prf (obseq A x y))) (σ : Sub Δ Γ) :
  (cong A B f x y e) [σ]t = cong (A [σ]T) (B [σ]T) (f [σ]t) (x [σ]t) (y [σ]t) (e [σ]t).
Proof.
  reflexivity.
Qed.

(* Function extensionality *)

Definition funext {Γ : Con} (A : Ty Γ) (P : Ty (Γ ▸ A)) (f g : Tm Γ (Π A P))
  (e : Tm Γ (Prf (for_all A (obseq (El P) (app (A [wk A]t) (P [lift (wk A) A]t) (f [wk A]t) (var0 A))
                                          (app (A [wk A]t) (P [lift (wk A) A]t) (g [wk A]t) (var0 A)))))) :
  Tm Γ (Prf (obseq (El (Π A P)) f g)).
Proof.
  unshelve econstructor.
  - refine (fun γ => to_set_intro _ (fun a0 a1 ae => _)). change (eq0 (fsts A γ) (fsts A γ) a0 a1) in ae.
    change (eq0 (fsts P (mkPair γ a0)) (fsts P (mkPair γ a1)) (fsts (fsts f γ) a0) (fsts (fsts g γ) a1)).
    exact (trans0 (fsts P (mkPair γ a0)) (fsts P (mkPair γ a0)) (reflU0 (fsts P (mkPair γ a0))) (fsts P (mkPair γ a1))
                   (to_set_esc _ (fsts e γ) a0) (snds (fsts g γ) a0 a1 ae)).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substFunext {Γ Δ : Con} (A : Ty Γ) (P : Ty (Γ ▸ A)) (f g : Tm Γ (Π A P))
  (e : Tm Γ (Prf (for_all A (obseq (El P) (app (A [wk A]t) (P [lift (wk A) A]t) (f [wk A]t) (var0 A))
                                          (app (A [wk A]t) (P [lift (wk A) A]t) (g [wk A]t) (var0 A))))))
  (σ : Sub Δ Γ) : (funext A P f g e) [σ]t = funext (A [σ]t) (P [lift σ A]t) (f [σ]t) (g [σ]t) (e [σ]t).
Proof.
  reflexivity.
Qed.

(* Proposition extensionality *)

Definition propext {Γ : Con} (P Q : Tm Γ (Ω Γ)) (e : Tm Γ (Prf (conj (impl P Q) (impl Q P))))
  : Tm Γ (Prf (obseq (El (Ω Γ)) P Q)).
Proof.
  unshelve econstructor.
  - refine (fun γ => to_set_intro _ (sand_intro _ _)).
    + exact (fun p => sand_fst (to_set_esc _ (fsts e γ)) p).
    + exact (fun q => sand_snd (to_set_esc _ (fsts e γ)) q).
  - exact (fun γ0 γ1 γe => stt).
Defined.

Lemma substPropext {Γ Δ : Con} (P Q : Tm Γ (Ω Γ)) (e : Tm Γ (Prf (conj (impl P Q) (impl Q P)))) (σ : Sub Δ Γ)
  : (propext P Q e) [σ]t = propext (P [σ]t) (Q [σ]t) (e [σ]t).
Proof.
  reflexivity.
Qed.

(* Martin-Löf identity types *)

Definition idty {Γ : Con} (A : Ty Γ) (a b : Tm Γ A) : Ty Γ.
Proof.
  unshelve econstructor.
  - exact (fun γ => Id0 (fsts A γ) (fsts a γ) (fsts b γ)).
  - intros γ0 γ1 γe. constructor.
    + exact (snds A γ0 γ1 γe).
    + split. exact (snds a γ0 γ1 γe). exact (snds b γ0 γ1 γe).
Defined.

Lemma substIdty {Γ Δ : Con} (A : Ty Γ) (a b : Tm Γ A) (σ : Sub Δ Γ) : (idty A a b) [σ]t = idty (A [σ]t) (a [σ]t) (b [σ]t).
Proof.
  reflexivity.
Qed.

(* reflexivity *)

Definition idty_refl {Γ : Con} (A : Ty Γ) (a : Tm Γ A) : Tm Γ (idty A a a).
Proof.
  unshelve econstructor.
  - exact (fun γ => frefl).
  - intros. exact stt.
Defined.

Lemma substIdty_refl {Γ Δ : Con} (A : Ty Γ) (a : Tm Γ A) (σ : Sub Δ Γ) : (idty_refl A a) [σ]t = idty_refl (A [σ]t) (a [σ]t).
Proof.
  reflexivity.
Qed.

(* J eliminator *)

Definition idtySub {Γ : Con} (A : Ty Γ) (a b : Tm Γ A) (e : Tm Γ (idty A a b)) : Sub Γ (Γ ▸ A ▸ (idty (A [wk A]t) (a [wk A]t) (var0 A))).
Proof.
  unshelve econstructor.
  - exact (fun γ => mkPair (mkPair γ (fsts b γ)) (fsts e γ)).
  - exact (fun γ0 γ1 γe => mkAndEx (mkAndEx γe (snds b γ0 γ1 γe)) stt).
Defined.

Definition Jelim_aux {Γ : Con} (A : Ty Γ) (a : Tm Γ A) (P : TY (Γ ▸ A ▸ (idty (A [wk A]t) (a [wk A]t) (var0 A))))
  (prefl : TM Γ (P [idtySub A a a (idty_refl A a) ]T))
  (γ : El1 Γ) (b : El0 (fsts A γ)) (e : fordedId (El0 (fsts A γ)) (eq0 (fsts A γ) (fsts A γ)) (fsts a γ) b) :
  El1 (fsts P (mkPair (mkPair γ b) e)).
Proof.
  refine (fordedId_rect (El0 (fsts A γ)) (eq0 (fsts A γ) (fsts A γ)) (fsts a γ)
              (fun b e => El1 (fsts P (mkPair (mkPair γ b) e))) (fsts prefl γ) _ b e).
  intros b0 e0.
  refine (cast1 (fsts P (mkPair (mkPair γ (fsts a γ)) frefl))
            (fsts P (mkPair (mkPair γ b0) (@forded (El0 (fsts A γ)) (eq0 (fsts A γ) (fsts A γ)) (fsts a γ) b0 e0)))
            _ (fsts prefl γ)).
  refine (snds P _ _ _). exact (mkAndEx (mkAndEx (refl1 Γ γ) e0) stt).
Defined.

Definition Jelim_aux_e {Γ : Con} (A : Ty Γ) (a : Tm Γ A) (P : TY (Γ ▸ A ▸ (idty (A [wk A]t) (a [wk A]t) (var0 A))))
  (prefl : TM Γ (P [idtySub A a a (idty_refl A a) ]T))
  (γ0 γ1 : El1 Γ) (γe : eq1 Γ Γ γ0 γ1) (b0 : El0 (fsts A γ0)) (b1 : El0 (fsts A γ1)) (be : eq0 (fsts A γ0) (fsts A γ1) b0 b1)
  (e0 : fordedId (El0 (fsts A γ0)) (eq0 (fsts A γ0) (fsts A γ0)) (fsts a γ0) b0)
  (e1 : fordedId (El0 (fsts A γ1)) (eq0 (fsts A γ1) (fsts A γ1)) (fsts a γ1) b1) :
  eq1 (fsts P (mkPair (mkPair γ0 b0) e0)) (fsts P (mkPair (mkPair γ1 b1) e1)) (Jelim_aux A a P prefl γ0 b0 e0) (Jelim_aux A a P prefl γ1 b1 e1).
Proof.
  set (A0 := fsts A γ0). set (A1 := fsts A γ1). set (Ae := snds A γ0 γ1 γe).
  set (a0 := fsts a γ0). set (a1 := fsts a γ1). set (ae := snds a γ0 γ1 γe).
  destruct e0 as [ | b0 e0 ] ; destruct e1 as [ | b1 e1 ].
  - exact (snds prefl γ0 γ1 γe).
  - refine (trans1 (fsts P (mkPair (mkPair γ0 a0) frefl)) (fsts P (mkPair (mkPair γ1 a1) frefl)) _
                   (fsts P (mkPair (mkPair γ1 b1) (@forded (El0 A1) (eq0 A1 A1) a1 b1 e1))) (snds prefl γ0 γ1 γe) _).
    + refine (snds P _ _ _). exact (mkAndEx (mkAndEx γe ae) stt).
    + apply cast1_eq.
  - refine (trans1 (fsts P (mkPair (mkPair γ0 b0) (@forded (El0 A0) (eq0 A0 A0) a0 b0 e0)))
                   (fsts P (mkPair (mkPair γ0 a0) frefl)) _ (fsts P (mkPair (mkPair γ1 a1) frefl)) _ (snds prefl γ0 γ1 γe)).
    + refine (snds P _ _ _). exact (mkAndEx (mkAndEx (refl1 Γ γ0) (sym0 _ _ e0)) stt).
    + apply sym1. apply cast1_eq.
  - refine (trans1 (fsts P (mkPair (mkPair γ0 b0) (@forded (El0 A0) (eq0 A0 A0) a0 b0 e0)))
                   (fsts P (mkPair (mkPair γ0 a0) frefl)) _ (fsts P (mkPair (mkPair γ1 b1) (@forded (El0 A1) (eq0 A1 A1) a1 b1 e1)))
                   (b := fsts prefl γ0) _ _).
    + refine (snds P _ _ _). exact (mkAndEx (mkAndEx (refl1 Γ γ0) (sym0 _ _ e0)) stt).
    + apply sym1. apply cast1_eq.
    + refine (trans1 (fsts P (mkPair (mkPair γ0 a0) frefl)) (fsts P (mkPair (mkPair γ1 a1) frefl)) _
                     (fsts P (mkPair (mkPair γ1 b1) (@forded (El0 A1) (eq0 A1 A1) a1 b1 e1))) (snds prefl γ0 γ1 γe) _).
      * refine (snds P _ _ _). exact (mkAndEx (mkAndEx γe ae) stt).
      * apply cast1_eq.
Defined.

Definition Jelim {Γ : Con} (A : Ty Γ) (a : Tm Γ A) (P : TY (Γ ▸ A ▸ (idty (A [wk A]t) (a [wk A]t) (var0 A))))
  (prefl : TM Γ (P [idtySub A a a (idty_refl A a) ]T)) (b : Tm Γ A) (e : Tm Γ (idty A a b))
  : TM Γ (P [idtySub A a b e ]T).
Proof.
  unshelve econstructor.
  - exact (fun γ => Jelim_aux A a P prefl γ (fsts b γ) (fsts e γ)).
  - exact (fun γ0 γ1 γe => Jelim_aux_e A a P prefl γ0 γ1 γe (fsts b γ0) (fsts b γ1) (snds b γ0 γ1 γe) (fsts e γ0) (fsts e γ1)).
Defined.

Lemma substJelim {Γ Δ : Con} (A : Ty Γ) (a : Tm Γ A) (P : TY (Γ ▸ A ▸ (idty (A [wk A]t) (a [wk A]t) (var0 A))))
  (prefl : TM Γ (P [idtySub A a a (idty_refl A a) ]T)) (b : Tm Γ A) (e : Tm Γ (idty A a b)) (σ : Sub Δ Γ)
  : (Jelim A a P prefl b e) [σ]t = Jelim (A [σ]t) (a [σ]t) (P [lift (lift σ A) (idty (A [wk A]t) (a [wk A]t) (var0 A))]T) (prefl [σ]t) (b [σ]t) (e [σ]t).
Proof.
  reflexivity.
Qed.

(* The J eliminator satisfies β definitionally *)

Lemma idtyβ {Γ : Con} (A : Ty Γ) (a : Tm Γ A) (P : TY (Γ ▸ A ▸ (idty (A [wk A]t) (a [wk A]t) (var0 A))))
  (prefl : TM Γ (P [idtySub A a a (idty_refl A a) ]T))
  : Jelim A a P prefl a (idty_refl A a) = prefl.
Proof.
  reflexivity.
Qed.

(* The identity type is logically equivalent to the observational equality.
   Thus, it satisfies funext and propext *)

Definition obseq_of_idty {Γ : Con} (A : Ty Γ) (a b : Tm Γ A) (e : Tm Γ (idty A a b)) : Tm Γ (Prf (obseq (El A) a b)).
Proof.
  unshelve econstructor.
  - refine (fun γ => to_set_intro _ _).
    exact (obseq_of_fordedId (El0 (fsts A γ)) (eq0 (fsts A γ) (fsts A γ)) (refl0 (fsts A γ)) (fsts a γ) (fsts b γ) (fsts e γ)).
  - intros γ0 γ1 γe. exact stt.
Defined.

Lemma substObseq_of_idty {Γ Δ : Con} (A : Ty Γ) (a b : Tm Γ A) (e : Tm Γ (idty A a b)) (σ : Sub Δ Γ)
  : (obseq_of_idty A a b e) [σ]t = obseq_of_idty (A [σ]t) (a [σ]t) (b [σ]t) (e [σ]t).
Proof.
  reflexivity.
Qed.

Definition idty_of_obseq {Γ : Con} (A : Ty Γ) (a b : Tm Γ A) (e : Tm Γ (Prf (obseq (El A) a b))) : Tm Γ (idty A a b).
Proof.
  unshelve econstructor.
  - refine (fun γ => forded (to_set_esc _ _)).
    exact (fsts e γ).
  - intros γ0 γ1 γe. exact stt.
Defined.

Lemma substIdty_of_obseq {Γ Δ : Con} (A : Ty Γ) (a b : Tm Γ A) (e : Tm Γ (Prf (obseq (El A) a b))) (σ : Sub Δ Γ)
  : (idty_of_obseq A a b e) [σ]t = idty_of_obseq (A [σ]t) (a [σ]t) (b [σ]t) (e [σ]t).
Proof.
  reflexivity.
Qed.
