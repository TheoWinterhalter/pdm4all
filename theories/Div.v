(*** Non-termination *)

From Coq Require Import Utf8 RelationClasses List.
From PDM Require Import util structures guarded PURE GuardedPDM.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Import ListNotations.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(** Syntax monad *)

Inductive M A :=
| retᴹ (x : A)
| act_reqᴹ (p : Prop) (k : p → M A)
| act_iterᴹ (J B : Type) (f : J → M (J + B)%type) (i : J) (k : B → M A).
(* | act_fixᴹ (D C : Type) (F : (D → C) → (D → M C)) (i : D) (k : C → M A). *)
(* | act_fixᴹ (C : Type) (F : C → M C) (k : C → M A). *)

Derive NoConfusion for M.

Arguments retᴹ [_].
Arguments act_reqᴹ [_].
(* Arguments act_fixᴹ [_]. *)
Arguments act_iterᴹ [_].

Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
  match c with
  | retᴹ x => f x
  | act_reqᴹ p k => act_reqᴹ p (λ h, bindᴹ (k h) f)
  | act_iterᴹ J B g i k => act_iterᴹ J B g i (λ h, bindᴹ (k h) f)
  (* | act_fixᴹ D C F i k => act_fixᴹ D C F i (λ z, bindᴹ (k z) f) *)
  (* | act_fixᴹ C F k => act_fixᴹ C F (λ z, bindᴹ (k z) f) *)
  end.

#[export] Instance Monad_M : Monad M := {|
  ret := retᴹ ;
  bind := bindᴹ
|}.

#[export] Instance ReqMonad_M : ReqMonad M := {|
  req p := act_reqᴹ p (λ h, retᴹ h)
|}.

(* Definition fixᴹ [D C] F i :=
  act_fixᴹ D C F i (λ x, retᴹ x). *)

(* Definition fixᴹ [C] F :=
  act_fixᴹ C F (λ x, retᴹ x). *)

Definition iterᴹ [J A] (f : J → M (J + A)) (i : J) :=
  act_iterᴹ J A f i (λ x, ret x).

#[export] Instance M_laws : MonadLaws M.
Proof.
  constructor.
  - intros A B x f. reflexivity.
  - intros A c. induction c.
    + reflexivity.
    + simpl. f_equal. extensionality h. auto.
    + simpl. f_equal. extensionality x. auto.
  - intros A B C c f g.
    induction c.
    + simpl. reflexivity.
    + simpl. f_equal. extensionality h. auto.
    + simpl. f_equal. extensionality h. auto.
Qed.

(** Evaluation relation *)

Definition iter_one [J A] (f : J → M (J + A)) (i : J) :=
  bind (f i) (λ x,
    match x with
    | inl j => iterᴹ f j
    | inr v => ret v
    end
  ).

Reserved Notation "u ▹ v" (at level 80).

Inductive red {A} : M A → M A → Prop :=

| prove_req :
    ∀ p k h,
      act_reqᴹ p k ▹ k h

(* Not clear how to unfold fix properly *)
(* | unfold_fix :
    ∀ D C F i k,
      act_fixᴹ D C F i k ▹ ? *)

(* Not great operationally is it? We need a rule to make fix disappear *)
(* Not going to get one with this determistic thing. *)
(* | unfold_fix :
    ∀ C F k,
      act_fixᴹ C F k ▹ bind (fixᴹ F) (λ x, bind (F x) k) *)

| iter_step :
    ∀ J B f i k,
      act_iterᴹ J B f i k ▹ bind (iter_one f i) k

where "u ▹ v" := (red u v).

Derive Signature for red.

(* Finite reduction sequence *)
Reserved Notation "u ▹* v" (at level 80).

Inductive finred [A] : M A → M A → Prop :=
| finred_id : ∀ c, c ▹* c
| finred_step : ∀ x y z, x ▹ y → y ▹* z → x ▹* z

where "u ▹* v" := (finred u v).

Derive Signature for finred.

(* Infinite reduction sequence *)
Definition infred [A] (s : nat → M A) :=
  ∀ n, s n ▹ s (S n).

(* Lemmas about reduction *)

Lemma ret_red_inv :
  ∀ A (x : A) c,
    ret x ▹ c →
    False.
Proof.
  intros A x c h.
  depelim h.
Qed.

Lemma ret_finred_inv :
  ∀ A (x : A) c,
    ret x ▹* c →
    c = ret x.
Proof.
  intros A x c h.
  depelim h.
  - reflexivity.
  - exfalso. eapply ret_red_inv. eassumption.
Qed.

Lemma req_red_inv :
  ∀ A (pre : Prop) (k : pre → M A) c,
    act_reqᴹ pre k ▹ c →
    ∃ (h : pre), c = k h.
Proof.
  intros A pre k c h.
  depelim h.
  eexists. reflexivity.
Qed.

Lemma req_finred_ret_inv :
  ∀ A (pre : Prop) (k : pre → M A) x,
    act_reqᴹ pre k ▹* ret x →
    ∃ (h : pre), k h ▹* ret x.
Proof.
  intros A pre k x h.
  depelim h.
  lazymatch goal with
  | H : act_reqᴹ _ _ ▹ _ |- _ => rename H into hr
  end.
  apply req_red_inv in hr. destruct hr as [hpre e]. subst.
  exists hpre. assumption.
Qed.

(* Not directly about red *)
Lemma bind_ret_inv :
  ∀ A B (c : M A) (f : A → M B) x,
    bind c f = ret x →
    ∃ y, c = ret y ∧ f y = ret x.
Proof.
  intros A B c f x e.
  destruct c as [y | |]. all: simpl in e. 2-3: noconf e.
  exists y. split.
  - reflexivity.
  - assumption.
Qed.

Lemma iter_finred_ret_inv :
  ∀ A J B f i k (x : A),
    act_iterᴹ J B f i k ▹* ret x →
    bind (iter_one f i) k ▹* ret x.
Proof.
  intros A J B f i k x h.
  depelim h.
  lazymatch goal with
  | H : _ ▹ _ |- _ => rename H into hr
  end.
  depelim hr.
  assumption.
Qed.

Lemma bind_finred_ret_inv :
  ∀ A B c f x,
    bind (A:=A) (B:=B) c f ▹* ret x →
    (bind c f = ret x) ∨
    (∃ y, c ▹* ret y ∧ f y ▹* ret x).
Proof.
  intros A B c f x h.
  induction c as [A y | A p k ih | A J C g ihg i k ih] in B, f, x, h |- *.
  - simpl in h. right.
    exists y. split.
    + constructor.
    + exact h.
  - right.
    simpl in h. apply req_finred_ret_inv in h. destruct h as [hp h].
    apply ih in h. destruct h as [h|h].
    + apply bind_ret_inv in h. destruct h as [y [e1 e2]].
      exists y. split.
      * econstructor. 1: constructor.
        erewrite e1. constructor.
      * rewrite e2. constructor.
    + destruct h as [y [h1 h2]].
      exists y. split.
      * econstructor. 2: exact h1.
        constructor.
      * assumption.
  - right.
    simpl in h. apply iter_finred_ret_inv in h.
    unfold iter_one in h.
    (* Will assoc save me? *)
Admitted.

(** Specifiation monad *)

Inductive run A :=
| cnv (x : A)
| div.

Arguments cnv [_].
Arguments div {_}.

Definition preᵂ := Prop.
Definition postᵂ A := run A → Prop.

Definition W' A := postᵂ A → preᵂ.

Class Monotonous [A] (w : W' A) :=
  ismono : ∀ (P Q : postᵂ A), (∀ x, P x → Q x) → w P → w Q.

Definition W A := { w : W' A | Monotonous w }.

Definition as_wp [A] (w : W' A) `{h : Monotonous _ w} : W A :=
  exist _ w h.

Definition retᵂ' [A] (x : A) : W' A :=
  λ P, P (cnv x).

#[export] Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ' x).
Proof.
  intros P Q hPQ h.
  apply hPQ. apply h.
Qed.

Definition retᵂ [A] (x : A) : W A :=
  as_wp (retᵂ' x).

Definition bindᵂ' [A B] (w : W A) (wf : A → W B) : W' B :=
  λ P,
    val w (λ r,
      match r with
      | cnv x => val (wf x) P
      | div => P div
      end
    ).

#[export] Instance bindᵂ_ismono [A B] (w : W A) (wf : A → W B) :
  Monotonous (bindᵂ' w wf).
Proof.
  destruct w as [w mw].
  intros P Q hPQ h.
  eapply mw. 2: exact h.
  simpl. intros [x|] hf.
  - destruct (wf x) as [wf' mwf].
    eapply mwf. 2: exact hf.
    assumption.
  - apply hPQ. assumption.
Qed.

Definition bindᵂ [A B] (w : W A) (wf : A → W B) : W B :=
  as_wp (bindᵂ' w wf).

Definition reqᵂ' (p : Prop) : W' p :=
  λ P, ∃ (h : p), P (cnv h).

#[export] Instance reqᵂ_ismono : ∀ p, Monotonous (reqᵂ' p).
Proof.
  intros p. intros P Q hPQ h.
  destruct h as [hp h].
  exists hp. apply hPQ. assumption.
Qed.

Definition reqᵂ (p : Prop) : W p :=
  as_wp (reqᵂ' p).

#[export] Instance Monad_W : Monad W := {|
  ret := retᵂ ;
  bind := bindᵂ
|}.

#[export] Instance ReqMonad_W : ReqMonad W := {|
  req := reqᵂ
|}.

Definition wle [A] (w₀ w₁ : W A) : Prop :=
  ∀ P, val w₁ P → val w₀ P.

#[export] Instance WStOrder : Order W.
Proof.
  exists wle.
  intros A x y z h₁ h₂. intros P h.
  apply h₁. apply h₂.
  assumption.
Defined.

#[export] Instance WStMono : MonoSpec W.
Proof.
  constructor.
  intros A B w w' wf wf' hw hwf.
  intros P h.
  hnf. hnf in h.
  apply hw. destruct w' as [w' mw']. eapply mw'. 2: exact h.
  simpl. intros [x|] hf.
  - apply hwf. assumption.
  - assumption.
Qed.

Definition liftᵂ [A] (w : pure_wp A) : W A.
Proof.
  exists (λ P, val w (λ x, P (cnv x))).
  intros P Q hPQ h.
  destruct w as [w mw].
  eapply mw. 2: exact h.
  simpl. intros x. apply hPQ.
Defined.

#[export] Instance hlift : PureSpec W WStOrder liftᵂ.
Proof.
  constructor.
  intros A w f.
  intros P h.
  assert (hpre : val w (λ _, True)).
  { unfold liftᵂ in h.
    destruct w as [w hw].
    eapply hw. 2: exact h.
    auto.
  }
  cbv. exists hpre.
  pose proof (prf (f hpre)) as hf. simpl in hf.
  apply hf in h. assumption.
Qed.

(** Effect observation *)

Definition θ' [A] (c : M A) : W' A :=
  λ post,
    (∀ pre k, c ▹* act_reqᴹ pre k → pre) ∧
    (∀ x, c ▹* ret x → post (cnv x)) ∧
    (∀ s, infred s → s 0 = c → post div).

#[export] Instance θ_ismono : ∀ A (c : M A), Monotonous (θ' c).
Proof.
  intros A c. intros P Q hPQ h.
  split. 2: split.
  - apply h.
  - intros x hx. apply hPQ. apply h. apply hx.
  - intros s hs hs0. apply hPQ. eapply h. all: eassumption.
Qed.

Definition θ [A] (c : M A) : W A :=
  as_wp (θ' c).

#[export] Instance θ_lax : LaxMorphism θ.
Proof.
  constructor.
  - intros A x.
    intros P h. simpl. simpl in h. red in h.
    split. 2: split.
    + intros pre k hr.
      apply ret_finred_inv in hr. noconf hr.
    + intros y hr. apply ret_finred_inv in hr. noconf hr.
      assumption.
    + intros s hs hs0.
      pose proof (hs 0) as hr. rewrite hs0 in hr.
      apply ret_red_inv in hr. exfalso. assumption.
  - intros A B c f.
    intros P h. simpl. simpl in h. red in h.
    split. 2: split.
    + intros pre k hr. admit.
    + intros x hr. admit.
    + intros s hs hs0. admit.
Admitted.