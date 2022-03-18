(*** Non-termination *)

From Coq Require Import Utf8 RelationClasses List PropExtensionality
  Classical_Prop Lia IndefiniteDescription.
From PDM Require Import util structures guarded PURE.
From PDM Require PDM.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Import ListNotations.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Equations With UIP.

#[local] Instance UIP_all A : UIP A.
Proof.
  intros x y e e'.
  apply proof_irrelevance.
Qed.

(** Syntax monad *)

Inductive M A :=
| retᴹ (x : A)
| act_reqᴹ (p : Prop) (k : p → M A)
| act_iterᴹ (J B : Type) (f : J → M (J + B)%type) (i : J) (k : B → M A).

Derive NoConfusion NoConfusionHom for M.

Arguments retᴹ [_].
Arguments act_reqᴹ [_].
(* Arguments act_fixᴹ [_]. *)
Arguments act_iterᴹ [_].

Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
  match c with
  | retᴹ x => f x
  | act_reqᴹ p k => act_reqᴹ p (λ h, bindᴹ (k h) f)
  | act_iterᴹ J B g i k => act_iterᴹ J B g i (λ h, bindᴹ (k h) f)
  end.

#[export] Instance Monad_M : Monad M := {|
  ret := retᴹ ;
  bind := bindᴹ
|}.

#[export] Instance ReqMonad_M : ReqMonad M := {|
  req p := act_reqᴹ p (λ h, retᴹ h)
|}.

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

(* Infinite reduction sequence from c *)
Definition infred [A] (s : nat → M A) (c : M A) :=
  c = s 0 ∧ ∀ n, s n ▹ s (S n).

(* The term c is not stuck on any require *)
Definition unstuck [A] (c : M A) :=
  ∀ pre k, c ▹* act_reqᴹ pre k → pre.

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

Lemma req_finred_inv :
  ∀ A (pre : Prop) (k : pre → M A) c,
    act_reqᴹ pre k ▹* c →
    (act_reqᴹ pre k = c) ∨ (∃ (h : pre), k h ▹* c).
Proof.
  intros A pre k c h.
  depelim h.
  - left. reflexivity.
  - lazymatch goal with
    | H : act_reqᴹ _ _ ▹ _ |- _ => rename H into hr
    end.
    apply req_red_inv in hr. destruct hr as [hpre e]. subst.
    right. exists hpre. assumption.
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

Lemma iter_finred_ret_inv_step :
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

Lemma bind_red :
  ∀ A B (c : M A) (f : A → M B) c',
    c ▹ c' →
    bind c f ▹ bind c' f.
Proof.
  intros A B c f c' h.
  induction h.
  - simpl. refine (prove_req _ _ _).
  - rewrite assoc. refine (iter_step _ _ _ _ _).
Qed.

Lemma bind_finred :
  ∀ A B (c : M A) (f : A → M B) c',
    c ▹* c' →
    bind c f ▹* bind c' f.
Proof.
  intros A B c f c' h.
  induction h.
  - constructor.
  - econstructor.
    + apply bind_red. eassumption.
    + assumption.
Qed.

Lemma finred_eq :
  ∀ A (u v : M A),
    u = v →
    u ▹* v.
Proof.
  intros A u v h.
  subst. constructor.
Qed.

Lemma finred_trans :
  ∀ A (u v w : M A),
    u ▹* v →
    v ▹* w →
    u ▹* w.
Proof.
  intros A u v w h1 h2.
  induction h1 as [| ????? ih] in w, h2 |- *.
  - assumption.
  - econstructor. 1: eassumption.
    apply ih. assumption.
Qed.

Lemma bind_red_inv :
  ∀ A B c f u,
    bind (A:=A) (B:=B) c f ▹ u →
    (∃ c', c ▹ c' ∧ u = bind c' f) ∨
    (∃ x, c = ret x ∧ f x ▹ u).
Proof.
  intros A B c f u h.
  destruct c as [ x | pre k | J C g i k ].
  - right. exists x. intuition auto.
  - simpl in h. depelim h.
    left. eexists. split. 2: reflexivity.
    constructor.
  - simpl in h. depelim h.
    left. eexists. split.
    + constructor.
    + rewrite assoc. reflexivity.
Qed.

Lemma bind_finred_inv :
  ∀ A B c f u,
    bind (A:=A) (B:=B) c f ▹* u →
    (∃ c', c ▹* c' ∧ u = bind c' f) ∨
    (∃ x, c ▹* ret x ∧ f x ▹* u).
Proof.
  intros A B c f u h.
  depind h.
  - left. eexists. split.
    + constructor.
    + reflexivity.
  - lazymatch goal with
    | H : _ ▹ _ |- _ => rename H into hr
    end.
    lazymatch goal with
    | H : ∀ (A : Type), _ |- _ => rename H into ih
    end.
    destruct c as [ x | pre k | J C g i k ].
    + simpl in hr. right.
      exists x. split.
      * constructor.
      * econstructor. all: eassumption.
    + simpl in hr. depelim hr.
      specialize ih with (1 := eq_refl).
      destruct ih as [[c' [hr e]] | [x [h1 h2]]].
      * subst. left.
        eexists. split. 2: reflexivity.
        econstructor. 2: exact hr.
        constructor.
      * right. eexists. split. 2: exact h2.
        econstructor. 2: exact h1.
        constructor.
    + simpl in hr. depelim hr.
      unfold iter_one in ih. change bindᴹ with bind in ih.
      rewrite <- !assoc in ih.
      specialize ih with (1 := eq_refl).
      destruct ih as [[c' [hr e]] | [x [h1 h2]]].
      * subst. left.
        eexists. split. 2: reflexivity.
        econstructor. 1: constructor.
        assumption.
      * right. eexists. split. 2: exact h2.
        econstructor. 1: constructor.
        unfold iter_one. rewrite !assoc in h1. rewrite assoc.
        assumption.
Qed.

Lemma bind_finred_ret_inv :
  ∀ A B c f x,
    bind (A:=A) (B:=B) c f ▹* ret x →
    ∃ y, c ▹* ret y ∧ f y ▹* ret x.
Proof.
  intros A B c f x h.
  apply bind_finred_inv in h. destruct h as [[c' [h e]] | h].
  - symmetry in e. apply bind_ret_inv in e.
    destruct e as [y [e1 e2]]. subst.
    exists y. split.
    + assumption.
    + rewrite e2. constructor.
  - assumption.
Qed.

Lemma not_finred_acc :
  ∀ A (c : M A),
    ¬ (∃ s, infred s c) →
    Acc (λ x y, y ▹ x) c.
Proof.
  intros A.
  pose (B := { u : M A | ¬ (Acc (λ x y, y ▹ x) u)}).
  assert (hnext : ∀ u : B, ∃ v : B, proj1_sig u ▹ proj1_sig v).
  { intros [u hu].
    eassert (h : ¬ _).
    { intro h. apply hu. apply Acc_intro. exact h. }
    apply not_forall_exists in h. destruct h as [v hv].
    apply imply_to_and in hv. destruct hv as [r hv].
    unshelve eexists ⟨ v ⟩. all: assumption.
  }
  intros c h.
  apply NNPP. intro hn. apply h. clear h.
  apply functional_choice in hnext.
  destruct hnext as [f hf].
  assert (he :
    ∃ s : nat → B,
      c = proj1_sig (s 0) ∧
      ∀ n, proj1_sig (s n) ▹ proj1_sig (s (S n))
  ).
  { unshelve eexists.
    { intro n. induction n as [| n b].
      - exists c. assumption.
      - exact (f b).
    }
    split.
    - simpl. reflexivity.
    - simpl. intro n. apply hf.
  }
  destruct he as [s hs].
  exists (λ n, proj1_sig (s n)). assumption.
Qed.

Lemma bind_infred_inv :
  ∀ A B c f s,
    infred s (bind (A:=A) (B:=B) c f) →
    (∃ s', infred s' c) ∨
    (∃ x s', c ▹* ret x ∧ infred s' (f x)).
Proof.
  intros A B c f s h.
  apply classical_right. intro hn.
  apply not_finred_acc in hn.
  induction hn as [c hc ih] in s, h |- *.
  destruct c as [ x | pre k | J C g i k ].
  - exists x, s. split.
    + constructor.
    + assumption.
  - simpl in h. destruct h as [e hs].
    specialize (hs 0) as hs0. rewrite <- e in hs0.
    depelim hs0.
    specialize ih with (s := λ n, s (S n)).
    edestruct ih as [x [s' [h1 h2]]].
    1:{ unshelve constructor. assumption. }
    1:{
      split.
      - symmetry. assumption.
      - intro n. apply hs.
    }
    exists x, s'. split.
    + econstructor. 1: constructor.
      eassumption.
    + assumption.
  - simpl in h. destruct h as [e hs].
    specialize (hs 0) as hs0. rewrite <- e in hs0.
    depelim hs0.
    specialize ih with (s := λ n, s (S n)).
    edestruct ih as [x [s' [h1 h2]]].
    1:{ constructor. }
    1:{
      split.
      - symmetry. rewrite assoc. assumption.
      - intro n. apply hs.
    }
    exists x, s'. split.
    + econstructor. 1: constructor.
      eassumption.
    + assumption.
Qed.

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

Definition as_wp [A] (w : W' A) {h : Monotonous w} : W A :=
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

#[export] Instance WOrder : Order W.
Proof.
  exists wle.
  intros A x y z h₁ h₂. intros P h.
  apply h₁. apply h₂.
  assumption.
Defined.

#[export] Instance WMono : MonoSpec W.
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

#[export] Instance hlift : PureSpec W WOrder liftᵂ.
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
    unstuck c ∧
    (∀ x, c ▹* ret x → post (cnv x)) ∧
    (∀ s, infred s c → post div).

#[export] Instance θ_ismono : ∀ A (c : M A), Monotonous (θ' c).
Proof.
  intros A c. intros P Q hPQ h.
  split. 2: split.
  - apply h.
  - intros x hx. apply hPQ. apply h. apply hx.
  - intros s hs. apply hPQ. eapply h. eassumption.
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
    + intros s hs.
      destruct hs as [e hs]. specialize (hs 0).
      rewrite <- e in hs.
      apply ret_red_inv in hs. contradiction.
  - intros A B c f.
    intros P h. simpl. simpl in h. red in h.
    destruct h as [huc [hcnv hdiv]].
    split. 2: split.
    + intros pre k hr.
      apply bind_finred_inv in hr.
      destruct hr as [[c' [hr e]] | [x [h1 h2]]].
      * {
        destruct c'. all: noconf e.
        - simpl in e. apply hcnv in hr. destruct hr as [huf [hcf hdf]].
          eapply huf. erewrite e. constructor.
        - eapply huc. eassumption.
      }
      * apply hcnv in h1. destruct h1 as [huf [hcf hdf]].
        eapply huf. eassumption.
    + intros x hr.
      apply bind_finred_ret_inv in hr.
      destruct hr as [y [h1 h2]].
      apply hcnv in h1. destruct h1 as [huf [hcf hdf]].
      apply hcf in h2. assumption.
    + intros s hs.
      apply bind_infred_inv in hs.
      destruct hs as [[s' hs'] | [x [s' [h1 h2]]]].
      * eapply hdiv. eassumption.
      * apply hcnv in h1. destruct h1 as [huf [hcf hdf]].
        eapply hdf. eassumption.
Qed.

#[export] Instance θ_reqlax : ReqLaxMorphism _ θ.
Proof.
  constructor.
  intros p.
  intros P h. simpl. simpl in h. red in h.
  destruct h as [h hP].
  split. 2: split.
  - intros pre k hr.
    apply req_finred_inv in hr.
    destruct hr as [e | [hpre hr]].
    + noconf e. assumption.
    + apply ret_finred_inv in hr. noconf hr.
  - intros x hr.
    assert (x = h) by apply proof_irrelevance. subst.
    assumption.
  - intros s hs.
    destruct hs as [e hs].
    specialize (hs 0) as h0. specialize (hs 1) as h1.
    rewrite <- e in h0. depelim h0.
    lazymatch goal with
    | e : _ = _ |- _ => rewrite e in h1
    end.
    depelim h1.
Qed.

Definition D A w : Type :=
  PDM.D (θ := θ) A w.

#[export] Instance DijkstraMonad_D : DijkstraMonad D :=
  PDM.DijkstraMonad_D WMono θ_lax.

(* Lift from PURE *)

Definition liftᴾ : ∀ A w, PURE A w → D A (liftᵂ w) :=
  PDM.liftᴾ (M := M) (W := W) WMono θ_lax θ_reqlax hlift.

(* Actions *)

Definition iterᵂ' [J A] (w : J → W (J + A)) (i : J) : W' A :=
  λ P,
    (* Finite iteration *)
    (∀ (js : list J) x,
      seqR (λ i j, val (w i) (λ r, r = cnv (inl j))) (i :: js) →
      val (w (last js i)) (λ r, r = cnv (inr x)) →
      P (cnv x)
    ) ∧
    (* Finite iteration with final branch diverging *)
    (∀ (js : list J),
      seqR (λ i j, val (w i) (λ r, r = cnv (inl j))) (i :: js) →
      val (w (last js i)) (λ r, r = div) →
      P div
    ) ∧
    (* Infinite iteration *)
    (∀ (js : nat → J),
      val (w i) (λ r, r = cnv (inl (js 0))) →
      (∀ n, val (w (js n)) (λ r, r = cnv (inl (js (S n))))) →
      P div
    ).

#[export] Instance iterᵂ_ismono [J A] (w : J → W (J + A)) (i : J) :
  Monotonous (iterᵂ' w i).
Proof.
  intros P Q hPQ h.
  destruct h as [hfi [hdb hdi]].
  split. 2: split.
  - intros js x hjs hl.
    apply hPQ. eapply hfi. all: eassumption.
  - intros js hjs hl.
    apply hPQ. eapply hdb. all: eassumption.
  - intros js hi hn.
    apply hPQ. eapply hdi. all: eassumption.
Qed.

Definition iterᵂ [J A] w i :=
  as_wp (@iterᵂ' A J w i).

Lemma θ_iter :
  ∀ J A (w : J → W (J + A)) (f : ∀ i, D (J + A) (w i)) (i : J),
    θ (iterᴹ (λ j, val (f j)) i) ≤ᵂ iterᵂ w i.
Proof.
  intros J A w f i.
  intros P h.
  simpl in h. red in h.
  simpl. split. 2: split.
  - intros pre k hr.
    (* Need iter_finred_req_inv *)
    admit.
  - intros x hr.
    (* Need iter_finred_ret_inv *)
    admit.
  - intros s hs.
    (* Will need iter_infred_inv *)
    admit.
Admitted.

Definition iterᴰ [J A] w (f : ∀ i, D (J + A) (w i)) (i : J) : D A (iterᵂ w i).
Proof.
  exists (iterᴹ (λ j, val (f j)) i).
  apply θ_iter.
Defined.