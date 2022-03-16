(*** Non-termination *)

From Coq Require Import Utf8 RelationClasses List PropExtensionality
  Classical_Prop Lia.
From PDM Require Import util structures guarded PURE GuardedPDM.
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

Lemma prove_finred :
  ∀ A (c : M A),
    (∀ n (c' : ∀ m, m ≤ n → M A), ∃ c'', c' n (le_n n) ▹ c'') →
    ∃ s, infred s c.
Proof.
  intros A c h.
  unfold infred.
  assert (hn :
    ∀ n,
      ∃ (c' : ∀ m, m ≤ n → M A),
        c' 0 (le_0_n _) = c ∧
        ∀ k hk hSk, c' k hk ▹ c' (S k) hSk
  ).
  { intro n. induction n as [| n ih].
    - exists (λ m hm, c). split.
      + reflexivity.
      + intros k hk hSk. lia.
    - destruct ih as [c' [e ih]].
      specialize (h _ c'). destruct h as [c'' hc''].
      unshelve eexists.
      { intros m hm.
        destruct (Compare_dec.le_gt_dec m n) as [hn|hn].
        - exact (c' _ hn).
        - exact c''.
      }
      split.
      + simpl. subst. f_equal. apply proof_irrelevance.
      + intros k hk hSk.
        destruct (Compare_dec.le_gt_dec k n) as [hn|]. 2: lia.
        destruct (Compare_dec.le_gt_dec (S k) n).
        * simpl. apply ih.
        * simpl. assert (k = n) by lia. subst.
          replace hn with (le_n n) by apply proof_irrelevance.
          assumption.
  }
  unshelve eexists.
  { intro n. specialize (hn n).
    (* Is there some way of doing this?
      Should I move to constructive stuff?
      Or simply to choice?
    *)
    admit.
  }
Abort.

Lemma bind_infred :
  ∀ A B c f s,
    infred s (bind (A:=A) (B:=B) c f) →
    unstuck c →
    (∃ s', infred s' c) ∨
    (∃ x s', c ▹* ret x ∧ infred s' (f x)).
Proof.
  intros A B c f s h huc.
  let p :=
    constr:(
      ∃ n (c' : ∀ m, m ≤ n → M A) x,
        (∀ m hm hSm, c' m hm ▹ c' (S m) hSm) ∧
        (∀ m hm, s m = bind (c' m hm) f) ∧
        c' 0 (le_0_n n) = c ∧
        c' n ltac:(auto) = ret x
    )
  in
  destruct (classic p) as [[n [c' [x [rm [em [e0 en]]]]]] | hh].
  - right. exists x, (λ q, s (q+n)). split.
    + rewrite <- e0, <- en. clear - rm.
      pose (m := n).
      set (h := le_0_n n). clearbody h.
      revert h. replace 0 with (n - m) by lia. intro h.
      clearbody m.
      induction m as [| m ih].
      * revert h. replace (n - 0) with n by lia. intro h.
        replace h with (le_n n) by apply proof_irrelevance.
        constructor.
      * {
        assert (h1 : n - m ≤ n) by lia.
        eapply finred_trans. 2: unshelve eapply ih. 2: assumption.
        destruct (classic (n ≤ m)) as [e|ne].
        - revert h h1.
          replace (n - S m) with 0 by lia.
          replace (n - m) with 0 by lia.
          intros. apply finred_eq. f_equal. apply proof_irrelevance.
        - assert (h2 : S (n - S m) ≤ n) by lia.
          econstructor. 1: unshelve eapply rm. 1: assumption.
          apply finred_eq.
          revert h1. replace (n - m) with (S (n - S m)) by lia. intro h1.
          f_equal. apply proof_irrelevance.
      }
    + split.
      * simpl. specialize (em n (le_n n)).
        rewrite en in em. simpl in em. symmetry. assumption.
      * intro m. apply h.
  - apply classical_left. intro hnc'.
    assert (hn :
      ∀ n (c' : ∀ m, m ≤ n → M A) x,
        ¬ (∀ m hm hSm, c' m hm ▹ c' (S m) hSm) ∨
        ¬ (∀ m hm, s m = bind (c' m hm) f) ∨
        c' 0 (le_0_n n) ≠ c ∨
        c' n ltac:(auto) ≠ ret x
    ).
    { intros n c' x.
      apply not_exists_forall in hh. unfold id in hh. specialize (hh n).
      apply not_exists_forall in hh. unfold id in hh. specialize (hh c').
      apply not_exists_forall in hh. unfold id in hh. specialize (hh x).
      apply not_and_or in hh. destruct hh as [hh|hh].
      1:{ left. assumption. }
      apply not_and_or in hh. destruct hh as [hh|hh].
      1:{ right. left. assumption. }
      apply not_and_or in hh.
      right. right. assumption.
    }
    clear hh.
    assert (hnc : ∀ x s', ¬ (c ▹* ret x) ∨ ¬ infred s' (f x)).
    { intros x s'.
      apply not_exists_forall in hnc'. unfold id in hnc'. specialize (hnc' x).
      apply not_exists_forall in hnc'. unfold id in hnc'. specialize (hnc' s').
      apply not_and_or in hnc'. assumption.
    }
    clear hnc'.
    destruct h as [e h].
    (* Now I want to apply bind_ret_inv to h n forall n
      and hopefully use hn to exclude the reduce to ret option.
      I might need to turn the goal into a ∀ n, ∃ c' : M A to build it step
      by step.
    *)
Abort.

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
    + intros s hs. admit.
Admitted.