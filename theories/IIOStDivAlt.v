(*** Non-termination with instrumented I/O and state

  The partial Dijstra Monad comes with a computation monad that is essentially
  a syntax monad (using a free monad) and the specification gives meaning to
  the different operations, including the iteration operator.

  For I/O we assume we can open and close files as well as read them.
  Because I/O is instrumented we can also read the history up to now.

  Variant of IIOStDiv but without trying to get rid of silent (tau) steps.

*)

From Coq Require Import Utf8 RelationClasses List PropExtensionality
  FunctionalExtensionality Arith Lia.
From PDM Require Import util structures guarded PURE.
From PDM Require PDM.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

From ITree Require ITree ITreeFacts.

Import ListNotations.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Set Equations Transparent.

Section IIOStDiv.

  Context (state path file_descr file_content : Type).

  (** I/O events *)

  Inductive event :=
  | EOpen (fp : path) (fd : file_descr)
  | ERead (fd : file_descr) (fc : file_content)
  | EClose (fd : file_descr).

  Definition trace :=
    list event.

  (* Reverse order from trace: last event first *)
  Definition history :=
    list event.

  (* Infinite runs have potentially infinite traces *)
  Inductive strace :=
  | fintrace (t : trace)
  | inftrace (s : nat → event).

  (* Truncation of a stream of traces *)
  Definition ttrunc (s : nat → trace) (n : nat) : trace :=
    concat (strunc s n).

  (* Traces including silent steps (tau from itrees) *)

  Definition otrace :=
    list (option event).

  Definition sotrace :=
    nat → option event.

  Fixpoint to_trace (t : otrace) : trace :=
    match t with
    | [] => []
    | Some e :: t => e :: to_trace t
    | None :: t => to_trace t
    end.

  Definition sotrace_refine (t : strace) (s : sotrace) : Prop :=
    match t with
    | fintrace t => ∃ n, ∀ m, n ≤ m → t = to_trace (strunc s m)
    | inftrace t => ∀ n, ∃ m, strunc t n = to_trace (strunc s m)
    end.

  Notation "t ⊆ s" := (sotrace_refine t s) (at level 80).

  (* A sotrace refining a stream of traces *)
  Definition trace_refine (t : sotrace) (s : nat → trace) : Prop :=
    ∀ n, ∃ m k, n ≤ m ∧ to_trace (strunc t m) = ttrunc s k.

  Notation "t ⊑ s" := (trace_refine t s) (at level 80).

  Definition embeds (s s' : sotrace) : Prop :=
    ∀ n, ∃ m, to_trace (strunc s' n) = to_trace (strunc s m).

  Definition uptotau (s s' : sotrace) : Prop :=
    embeds s s' ∧ embeds s' s.

  Fixpoint stream_prepend [A] (l : list A) (s : nat → A) (n : nat) : A :=
    match l, n with
    | [], n => s n
    | x :: l, 0 => x
    | x :: l, S n => stream_prepend l s n
    end.

  Definition strace_prepend (tr : trace) (st : strace) : strace :=
    match st with
    | fintrace tr' => fintrace (tr ++ tr')
    | inftrace s => inftrace (stream_prepend tr s)
    end.

  (* TODO MOVE *)
  Definition stream_skipn [A] (s : nat → A) (n : nat) : nat → A :=
    λ m, s (n + m).

  Lemma stream_prepend_app :
    ∀ A t t' (s : nat → A),
      stream_prepend t (stream_prepend t' s) = stream_prepend (t ++ t') s.
  Proof.
    intros A t t' s.
    extensionality n.
    induction t as [| a t ih] in t', s, n |- *.
    - simpl. reflexivity.
    - destruct n.
      + simpl. reflexivity.
      + simpl. apply ih.
  Qed.

  Lemma stream_prepend_skipn :
    ∀ A (s : nat → A) n,
      stream_prepend (strunc s n) (stream_skipn s n) = s.
  Proof.
    intros A s n. extensionality m.
    induction n as [| n ih] in s, m |- *.
    - simpl. reflexivity.
    - destruct m.
      + simpl. reflexivity.
      + simpl. rewrite ih. reflexivity.
  Qed.

  Lemma strunc_length :
    ∀ A (s : nat → A) n,
      length (strunc s n) = n.
  Proof.
    intros A s n.
    induction n as [| n ih] in s |- *.
    - simpl. reflexivity.
    - simpl. f_equal. apply ih.
  Qed.

  Lemma strace_prepend_nil :
    ∀ s,
      strace_prepend [] s = s.
  Proof.
    intros [].
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma strace_prepend_app :
    ∀ t t' s,
      strace_prepend t (strace_prepend t' s) = strace_prepend (t ++ t') s.
  Proof.
    intros t t' [].
    - simpl. rewrite app_assoc. reflexivity.
    - simpl. rewrite stream_prepend_app. reflexivity.
  Qed.

  Lemma strunc_stream_prepend_ge :
    ∀ A (l : list A) s n,
      n ≥ length l →
      strunc (stream_prepend l s) n = l ++ strunc s (n - length l).
  Proof.
    intros A l s n hn.
    induction l as [| x l ih] in s, n, hn |- *.
    - simpl. f_equal. lia.
    - simpl in hn.
      destruct n as [| n]. 1: lia.
      cbn - [strace_prepend]. f_equal. apply ih. lia.
  Qed.

  Lemma strunc_stream_prepend_le :
    ∀ A (l : list A) s n,
      n ≤ length l →
      strunc (stream_prepend l s) n = firstn n l.
  Proof.
    intros A l s n hn.
    induction l as [| x l ih] in s, n, hn |- *.
    - simpl in hn. destruct n. 2: lia.
      simpl. reflexivity.
    - simpl in hn.
      destruct n as [| n].
      + reflexivity.
      + cbn - [strace_prepend]. f_equal. apply ih. lia.
  Qed.

  Lemma to_trace_app :
    ∀ t t',
      to_trace (t ++ t') = to_trace t ++ to_trace t'.
  Proof.
    intros t t'.
    induction t as [| [] ? ih] in t' |- *.
    - reflexivity.
    - simpl. f_equal. apply ih.
    - simpl. apply ih.
  Qed.

  Lemma sotrace_refine_prepend :
    ∀ tr t s,
      t ⊆ s →
      strace_prepend (to_trace tr) t ⊆ stream_prepend tr s.
  Proof.
    intros tr t s h.
    destruct t as [t | t].
    - simpl in *. destruct h as [n h].
      exists (length tr + n). intros m hm.
      rewrite strunc_stream_prepend_ge. 2: lia.
      rewrite to_trace_app. f_equal.
      apply h. lia.
    - simpl in *. intro n.
      destruct (dec_le n (length (to_trace tr))) as [hn | hn].
      + rewrite strunc_stream_prepend_le. 2: assumption.
        induction tr as [| [] tr ih] in n |- *.
        * exists 0. simpl. rewrite firstn_nil. reflexivity.
        * {
          cbn - [stream_prepend].
          destruct n as [| n].
          - exists 0. reflexivity.
          - cbn - [stream_prepend].
            destruct (ih n) as [m em].
            exists (S m). simpl. f_equal. apply em.
        }
        * {
          cbn - [stream_prepend].
          destruct (ih n) as [m em].
          exists (S m). simpl. apply em.
        }
      + rewrite strunc_stream_prepend_ge. 2: lia.
        destruct (h (n - length (to_trace tr))) as [m em].
        rewrite em.
        induction tr as [| [] tr ih] in |- *.
        * cbn - [stream_prepend]. exists m. reflexivity.
        * cbn - [stream_prepend].
          destruct ih as [m' e'].
          exists (S m'). simpl. f_equal. assumption.
        * cbn - [stream_prepend].
          destruct ih as [m' e'].
          exists (S m'). simpl. assumption.
  Qed.

  Lemma embeds_refl :
    ∀ s, embeds s s.
  Proof.
    intro s. intro n.
    exists n. reflexivity.
  Qed.

  Lemma uptotau_refl :
    ∀ s, uptotau s s.
  Proof.
    intro s. split. all: apply embeds_refl.
  Qed.

  Lemma embeds_prepend :
    ∀ t t' s s',
      to_trace t = to_trace t' →
      embeds s s' →
      embeds (stream_prepend t s) (stream_prepend t' s').
  Proof.
    intros t t' s s' ht hs.
    intro n.
    destruct (dec_le n (length t')) as [hn | hn].
    - rewrite strunc_stream_prepend_le. 2: lia.
      induction n as [| n ih] in t, t', ht |- *.
      + exists 0. reflexivity.
      + destruct t' as [| [] t'].
        * rewrite firstn_nil. simpl. exists 0. reflexivity.
        * {
          simpl. simpl in ht.
          induction t as [| [] t iht] in e, t', ht |- *.
          - discriminate.
          - simpl in ht. noconf ht.
            specialize (ih t t').
            forward ih. { assumption. }
            destruct ih as [m ih].
            exists (S m). simpl. f_equal. assumption.
          - simpl in ht. eapply iht in ht. destruct ht as [m h].
            exists (S m). simpl. assumption.
        }
        * simpl. apply ih. assumption.
    - rewrite strunc_stream_prepend_ge. 2: lia.
      rewrite to_trace_app. rewrite <- ht.
      specialize (hs (n - length t')). destruct hs as [m hm].
      rewrite hm.
      exists (m + length t). rewrite strunc_stream_prepend_ge. 2: lia.
      rewrite to_trace_app. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma uptotau_prepend :
    ∀ t t' s s',
      to_trace t = to_trace t' →
      uptotau s s' →
      uptotau (stream_prepend t s) (stream_prepend t' s').
  Proof.
    intros t t' s s' ht [].
    split.
    all: apply embeds_prepend. all: eauto.
  Qed.

  Fixpoint is_open (fd : file_descr) (hist : history) : Prop :=
    match hist with
    | EOpen fp fd' :: hh => fd = fd' ∨ is_open fd hh
    | EClose fd' :: hh => fd ≠ fd' ∧ is_open fd hh
    | _ :: hh => is_open fd hh
    | [] => False
    end.

  (** Syntax monad *)

  Inductive M A :=
  | retᴹ (x : A)
  | act_reqᴹ (p : Prop) (k : p → M A)
  | act_iterᴹ (J B : Type) (f : J → M (J + B)%type) (i : J) (k : B → M A)
  | act_getᴹ (k : state → M A)
  | act_putᴹ (s : state) (k : M A)
  | act_openᴹ (p : path) (k : file_descr → M A)
  | act_readᴹ (f : file_descr) (k : file_content → M A)
  | act_closeᴹ (f : file_descr) (k : M A)
  | act_histᴹ (k : history → M A).

  Arguments retᴹ [_].
  Arguments act_reqᴹ [_].
  Arguments act_iterᴹ [_].
  Arguments act_getᴹ [_].
  Arguments act_putᴹ [_].
  Arguments act_openᴹ [_].
  Arguments act_readᴹ [_].
  Arguments act_closeᴹ [_].
  Arguments act_histᴹ [_].

  Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    match c with
    | retᴹ x => f x
    | act_reqᴹ p k => act_reqᴹ p (λ h, bindᴹ (k h) f)
    | act_iterᴹ J B g i k => act_iterᴹ J B g i (λ h, bindᴹ (k h) f)
    | act_getᴹ k => act_getᴹ (λ s, bindᴹ (k s) f)
    | act_putᴹ s k => act_putᴹ s (bindᴹ k f)
    | act_openᴹ fp k => act_openᴹ fp (λ x, bindᴹ (k x) f)
    | act_readᴹ fd k => act_readᴹ fd (λ x, bindᴹ (k x) f)
    | act_closeᴹ fd k => act_closeᴹ fd (bindᴹ k f)
    | act_histᴹ k => act_histᴹ (λ x, bindᴹ (k x) f)
    end.

  #[export] Instance Monad_M : Monad M := {|
    ret := retᴹ ;
    bind := bindᴹ
  |}.

  #[export] Instance ReqMonad_M : ReqMonad M := {|
    req p := act_reqᴹ p (λ h, retᴹ h)
  |}.

  Definition iterᴹ [J A] (f : J → M (J + A)) (i : J) : M A :=
    act_iterᴹ J A f i (λ x, ret x).

  Definition getᴹ : M state :=
    act_getᴹ (λ x, ret x).

  Definition putᴹ (s : state) : M unit :=
    act_putᴹ s (ret tt).

  Definition openᴹ fp :=
    act_openᴹ fp (λ x, ret x).

  Definition readᴹ fd :=
    act_readᴹ fd (λ x, ret x).

  Definition closeᴹ fd :=
    act_closeᴹ fd (ret tt).

  Definition histᴹ :=
    act_histᴹ (λ x, ret x).

  #[export] Instance M_laws : MonadLaws M.
  Proof.
    constructor.
    - intros A B x f. reflexivity.
    - intros A c. induction c.
      1: reflexivity.
      all: simpl ; f_equal ; try apply functional_extensionality ; auto.
    - intros A B C c f g.
      induction c.
      1: reflexivity.
      all: simpl ; f_equal ; try apply functional_extensionality ; auto.
  Qed.

  (** Specification monad from Dijkstra Monads for ever *)

  (* Similar to itrace *)
  Inductive run A :=
  | cnv (t : otrace) (s : state) (x : A)
  | div (s : sotrace).

  Arguments cnv [_].
  Arguments div [_].

  (* Equal up to tau *)
  Definition eutt [A] (r r' : run A) : Prop :=
    match r, r' with
    | cnv t s x, cnv t' s' x' =>
      to_trace t = to_trace t' ∧ s = s' ∧ x = x'
    | div s, div s' =>
      uptotau s s'
    | _, _ => False
    end.

  Notation "u ≈ v" := (eutt u v) (at level 70).

  Lemma eutt_refl :
    ∀ A (r : run A),
      r ≈ r.
  Proof.
    intros A r.
    destruct r.
    - simpl. intuition reflexivity.
    - simpl. apply uptotau_refl.
  Qed.

  Definition resp_eutt [A] (p : run A → Prop) : Prop :=
    ∀ r r', r ≈ r' → p r → p r'.

  Definition preᵂ :=
    history → state → Prop.

  Definition postᵂ A :=
    { post : run A → Prop | resp_eutt post }.

  Definition W' A := postᵂ A → preᵂ.

  Class Monotonous [A] (w : W' A) :=
    ismono :
      ∀ (P Q : postᵂ A),
        (∀ x, val P x → val Q x) →
        ∀ hist s₀, w P hist s₀ → w Q hist s₀.

  Definition W A := { w : W' A | Monotonous w }.

  Definition as_wp [A] (w : W' A) {h : Monotonous w} : W A :=
    exist _ w h.

  Instance Monotonous_val [A] (w : W A) : Monotonous (val w).
  Proof.
    destruct w. assumption.
  Qed.

  Definition retᵂ' [A] (x : A) : W' A :=
    λ P hist s₀, val P (cnv [] s₀ x).

  #[export] Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ' x).
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. apply h.
  Qed.

  Definition retᵂ [A] (x : A) : W A :=
    as_wp (retᵂ' x).

  #[tactic=idtac] Equations? shift_post [A] (tr : otrace) (P : postᵂ A) : postᵂ A :=
    shift_post tr P :=
      ⟨ λ r,
          match r with
          | cnv tr' s x => val P (cnv (tr ++ tr') s x)
          | div st => val P (div (stream_prepend tr st))
          end
      ⟩.
  Proof.
    intros r r' h hp.
    destruct P as [P hP].
    destruct r as [t s x | s], r' as [t' s' x' | s']. 2,3: contradiction.
    - simpl in *. eapply hP. 2: eassumption.
      simpl. intuition subst.
      rewrite !to_trace_app. f_equal. assumption.
    - simpl in *. eapply hP. 2: eassumption.
      simpl. apply uptotau_prepend. all: auto.
  Qed.

  Lemma shift_post_nil :
    ∀ A (P : postᵂ A) r,
      val (shift_post [] P) r → val P r.
  Proof.
    intros A P r h.
    destruct r. all: assumption.
  Qed.

  #[tactic=idtac] Equations? bindᵂ' [A B] (w : W A) (wf : A → W B) : W' B :=
    bindᵂ' w wf :=
      λ P hist s₀,
        val w ⟨ λ r,
          match r with
          | cnv tr s₁ x => val (wf x) (shift_post tr P) (rev_append (to_trace tr) hist) s₁
          | div s => val P (div s)
          end
        ⟩ hist s₀.
  Proof.
    intros r r' h hp.
    destruct P as [P hP].
    destruct r as [t s x | s], r' as [t' s' x' | s']. 2,3: contradiction.
    - simpl in h. destruct h as [et [es ex]]. subst.
      rewrite <- et. eapply ismono. 2: eassumption.
      intros [].
      + simpl. apply hP. simpl.
        intuition auto.
        rewrite !to_trace_app. f_equal. assumption.
      + simpl. apply hP. simpl.
        apply uptotau_prepend.
        * assumption.
        * apply uptotau_refl.
    - simpl in *. eapply hP. 2: eassumption.
      simpl. assumption.
  Qed.

  #[export] Instance bindᵂ_ismono [A B] (w : W A) (wf : A → W B) :
    Monotonous (bindᵂ' w wf).
  Proof.
    destruct w as [w mw].
    intros P Q hPQ hist s₀ h.
    eapply mw. 2: exact h.
    simpl. intros [tr s₁ x| st] hf.
    - destruct (wf x) as [wf' mwf].
      eapply mwf. 2: exact hf.
      intros [] hr.
      + simpl. apply hPQ. assumption.
      + simpl. apply hPQ. assumption.
    - apply hPQ. assumption.
  Qed.

  Definition bindᵂ [A B] (w : W A) (wf : A → W B) : W B :=
    as_wp (bindᵂ' w wf).

  Definition reqᵂ' (p : Prop) : W' p :=
    λ P hist s₀, ∃ (h : p), val P (cnv [] s₀ h).

  #[export] Instance reqᵂ_ismono : ∀ p, Monotonous (reqᵂ' p).
  Proof.
    intros p. intros P Q hPQ hist s₀ h.
    destruct h as [hp h].
    exists hp. apply hPQ. assumption.
  Qed.

  Definition reqᵂ (p : Prop) : W p :=
    as_wp (reqᵂ' p).

  Definition tauᵂ' : W' unit :=
    λ P hist s₀, val P (cnv [ None ] s₀ tt).

  #[export] Instance tauᵂ_ismono : Monotonous tauᵂ'.
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. assumption.
  Qed.

  Definition tauᵂ : W unit :=
    as_wp tauᵂ'.

  Definition getᵂ' : W' state :=
    λ P hist s, val P (cnv [] s s).

  Instance getᵂ_ismono : Monotonous getᵂ'.
  Proof.
    intros P Q hPQ hist s₀ h.
    red. red in h.
    apply hPQ. assumption.
  Qed.

  Definition getᵂ : W state :=
    as_wp getᵂ'.

  Definition putᵂ' (s : state) : W' unit :=
    λ P hist s₀, val P (cnv [] s tt).

  Instance putᵂ_ismono : ∀ s, Monotonous (putᵂ' s).
  Proof.
    intros s. intros P Q hPQ hist s₀ h.
    apply hPQ. assumption.
  Qed.

  Definition putᵂ (s : state) : W unit :=
    as_wp (putᵂ' s).

  Definition openᵂ' (fp : path) : W' file_descr :=
    λ P hist s₀, ∀ fd, val P (cnv [ Some (EOpen fp fd) ] s₀ fd).

  Instance openᵂ_ismono : ∀ fp, Monotonous (openᵂ' fp).
  Proof.
    intros fp. intros P Q hPQ hist s₀ h.
    intro fd.
    apply hPQ. apply h.
  Qed.

  Definition openᵂ (fp : path) : W file_descr :=
    as_wp (openᵂ' fp).

  Definition readᵂ' (fd : file_descr) : W' file_content :=
    λ P hist s₀, is_open fd hist ∧ ∀ fc, val P (cnv [ Some (ERead fd fc) ] s₀ fc).

  Instance readᵂ_ismono : ∀ fd, Monotonous (readᵂ' fd).
  Proof.
    intros fd. intros P Q hPQ hist s₀ h.
    destruct h as [ho h].
    split.
    - assumption.
    - intro fc. apply hPQ. apply h.
  Qed.

  Definition readᵂ (fd : file_descr) : W file_content :=
    as_wp (readᵂ' fd).

  Definition closeᵂ' (fd : file_descr) : W' unit :=
    λ P hist s₀, is_open fd hist ∧ val P (cnv [ Some (EClose fd) ] s₀ tt).

  Instance closeᵂ_ismono : ∀ fd, Monotonous (closeᵂ' fd).
  Proof.
    intros fd. intros P Q hPQ hist s₀ h.
    destruct h as [ho h].
    split.
    - assumption.
    - apply hPQ. assumption.
  Qed.

  Definition closeᵂ (fd : file_descr) : W unit :=
    as_wp (closeᵂ' fd).

  Definition histᵂ' : W' history :=
    λ P hist s₀, val P (cnv [] s₀ hist).

  Instance histᵂ_ismono : Monotonous histᵂ'.
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. assumption.
  Qed.

  Definition histᵂ : W history :=
    as_wp histᵂ'.

  #[export] Instance Monad_W : Monad W := {|
    ret := retᵂ ;
    bind := bindᵂ
  |}.

  #[export] Instance ReqMonad_W : ReqMonad W := {|
    req := reqᵂ
  |}.

  Definition wle [A] (w₀ w₁ : W A) : Prop :=
    ∀ P hist s₀, val w₁ P hist s₀ → val w₀ P hist s₀.

  #[export] Instance Order_W : Order W.
  Proof.
    exists wle.
    intros A x y z h₁ h₂. intros P hist s₀ h.
    apply h₁. apply h₂.
    assumption.
  Defined.

  #[export] Instance Reflexive_wle [A] : Reflexive (wle (A := A)).
  Proof.
    intro w. intros p hist s₀ h. assumption.
  Qed.

  #[export] Instance MonoSpec_W : MonoSpec W.
  Proof.
    constructor.
    intros A B w w' wf wf' hw hwf.
    intros P hist s₀ h.
    hnf. hnf in h.
    apply hw. destruct w' as [w' mw']. eapply mw'. 2: exact h.
    simpl. intros [tr s₁ x| st] hf.
    - apply hwf. assumption.
    - assumption.
  Qed.

  (** Specification of iter using an impredicative encoding *)

  Definition iter_expand [J A] (w : J → W (J + A)) (i : J) (k : J → W A) : W A :=
    bind (w i) (λ x,
      match x with
      | inl j => bind tauᵂ (λ _, k j)
      | inr y => ret y
      end
    ).

  Lemma iter_expand_mono :
    ∀ J A (w w' : J → W (J + A)) (i : J) (k : J → W A),
      w i ≤ᵂ w' i →
      iter_expand w i k ≤ᵂ iter_expand w' i k.
  Proof.
    intros J A w w' i k hw.
    unfold iter_expand. eapply bind_mono.
    - apply hw.
    - intro. reflexivity.
  Qed.

  (** Greatest fixpoint of [iter_expand w j (iterᵂ' w) ≤ᵂ iterᵂ' w j] *)
  Definition iterᵂ' [J A] (w : J → W (J + A)) (i : J) : W' A :=
    λ post hist s₀,
      ∃ (P : J → W A),
        (∀ j, iter_expand w j P ≤ᵂ P j) ∧
        val (P i) post hist s₀.

  #[export] Instance iterᵂ_ismono [J A] (w : J → W (J + A)) (i : J) :
    Monotonous (iterᵂ' w i).
  Proof.
    intros P Q hPQ hist s₀ h.
    destruct h as [iᵂ [helim hi]].
    exists iᵂ. split.
    - apply helim.
    - eapply ismono.
      + eapply hPQ.
      + assumption.
  Qed.

  Definition iterᵂ [J A] w i :=
    as_wp (@iterᵂ' J A w i).

  Lemma iterᵂ_unfold :
    ∀ J A (w : J → W (J + A)) (i : J),
      iter_expand w i (iterᵂ w) ≤ᵂ iterᵂ w i.
  Proof.
    intros J A w i. intros post hist s₀ h.
    destruct h as [iᵂ [helim hi]].
    eapply helim in hi as h. simpl in h. red in h.
    simpl. red. eapply ismono. 2: exact h.
    simpl. intros [tr s₁ [j | x] | st] hh.
    - simpl. red.
      exists iᵂ. split. all: auto.
    - assumption.
    - assumption.
  Qed.

  Lemma iterᵂ_coind :
    ∀ J A (w : J → W (J + A)) (i : J) (w' : J → W A),
      (∀ j, iter_expand w j w' ≤ᵂ w' j) →
      iterᵂ w i ≤ᵂ w' i.
  Proof.
    intros J A w i w' h.
    intros post hist s₀ h'.
    exists w'. split. all: assumption.
  Qed.

  Lemma iterᵂ_fold :
    ∀ J A (w : J → W (J + A)) (i : J),
    iterᵂ w i ≤ᵂ iter_expand w i (iterᵂ w).
  Proof.
    intros J A w i.
    eapply iterᵂ_coind with (w' := λ i, iter_expand _ i _). clear i.
    intros i.
    eapply bind_mono. 1: reflexivity.
    intros [].
    - eapply bind_mono. 1: reflexivity.
      intros _. apply iterᵂ_unfold.
    - reflexivity.
  Qed.

  Definition liftᵂ [A] (w : pure_wp A) : W A.
  Proof.
    exists (λ P hist s₀, val w (λ x, val P (cnv [] s₀ x))).
    intros P Q hPQ hist s₀ h.
    destruct w as [w mw].
    eapply mw. 2: exact h.
    simpl. intros x. apply hPQ.
  Defined.

  #[export] Instance hlift : PureSpec W Order_W liftᵂ.
  Proof.
    constructor.
    intros A w f.
    intros P hist s₀ h.
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

  (* Effect observation *)

  Fixpoint θ [A] (c : M A) : W A :=
    match c with
    | retᴹ x => ret x
    | act_getᴹ k => bind getᵂ (λ x, θ (k x))
    | act_putᴹ s k => bind (putᵂ s) (λ _, θ k)
    | act_reqᴹ p k => bind (reqᵂ p) (λ x, θ (k x))
    | act_iterᴹ J B g i k => bind (iterᵂ (λ i, θ (g i)) i) (λ x, θ (k x))
    | act_openᴹ fp k => bind (openᵂ fp) (λ x, θ (k x))
    | act_readᴹ fd k => bind (readᵂ fd) (λ x, θ (k x))
    | act_closeᴹ fd k => bind (closeᵂ fd) (λ x, θ k)
    | act_histᴹ k => bind histᵂ (λ x, θ (k x))
    end.

  Lemma bindᵂ_assoc :
    ∀ A B C (w : W A) (wf : A → W B) (wg : B → W C),
      bind w (λ x, bind (wf x) wg) ≤ᵂ bind (bind w wf) wg.
  Proof.
    intros A B C w wf wg.
    intros P hist s₀ h.
    simpl. red.
    simpl in h. red in h.
    eapply ismono. 2: exact h.
    simpl. intros [].
    - intro hf. red.
      eapply ismono. 2: exact hf.
      simpl. intros [].
      + rewrite !rev_append_rev. rewrite to_trace_app.
        rewrite rev_app_distr. rewrite !app_assoc.
        intro hg.
        eapply ismono. 2: exact hg.
        intros [].
        * simpl. rewrite app_assoc. auto.
        * simpl. rewrite stream_prepend_app. auto.
      + auto.
    - auto.
  Qed.

  Instance θ_lax : LaxMorphism θ.
  Proof.
    constructor.
    - intros A x.
      reflexivity.
    - intros A B c f.
      induction c
      as [ A x | A p k ih | A J C g ihg i k ih | A k ih | A p k ih | A fp k ih | A fd k ih | A fd k ih | A k ih]
      in B, f |- *.
      2-9: cbn - [structures.wle bind].
      2-9: etransitivity ; [| eapply bindᵂ_assoc].
      2-9: cbn - [structures.wle].
      2-9: change bindᵂ with bind.
      2-9: eapply bind_mono ; [reflexivity |].
      2-9: intro.
      2-9: apply ih.
      intros P hist s₀ h.
      simpl. simpl in h.
      eapply ismono. 2: exact h.
      apply shift_post_nil.
  Qed.

  Instance θ_reqlax : ReqLaxMorphism _ θ.
  Proof.
    constructor.
    intros p. intros post hist s₀ h.
    simpl. red. simpl.
    simpl in h. red in h.
    destruct h as [hp h]. exists hp. assumption.
  Qed.

  (** Dijstra monad in the style of DM4ever *)

  Definition D A w : Type :=
    PDM.D (θ := θ) A w.

  Instance DijkstraMonad_D : DijkstraMonad D :=
    PDM.DijkstraMonad_D MonoSpec_W θ_lax.

  (* Lift from PURE *)

  Definition liftᴾ : ∀ A w, PURE A w → D A (liftᵂ w) :=
    PDM.liftᴾ (M := M) (W := W) MonoSpec_W θ_lax θ_reqlax hlift.

  (* Actions *)

  Definition iterᴰ [J A w] (f : ∀ (j : J), D (J + A) (w j)) i : D A (iterᵂ w i).
  Proof.
    exists (iterᴹ (λ j, val (f j)) i).
    intros P hist s₀ h.
    simpl. simpl in h.
    destruct h as [iᵂ [helim hi]].
    exists iᵂ. split.
    - intros j. etransitivity. 2: eapply helim.
      apply iter_expand_mono.
      eapply prf.
    - eapply ismono. 2: exact hi.
      intros [].
      + rewrite app_nil_r. auto.
      + auto.
  Defined.

  Definition getᴰ : D state getᵂ.
  Proof.
    exists getᴹ.
    intros P hist s₀ h. apply h.
  Defined.

  Definition putᴰ (s : state) : D unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    intros P hist s₀ h. apply h.
  Defined.

  Definition openᴰ fp : D file_descr (openᵂ fp).
  Proof.
    exists (openᴹ fp).
    intros P hist s₀ h. apply h.
  Defined.

  Definition readᴰ fd : D file_content (readᵂ fd).
  Proof.
    exists (readᴹ fd).
    intros P hist s₀ h. apply h.
  Defined.

  Definition closeᴰ fd : D unit (closeᵂ fd).
  Proof.
    exists (closeᴹ fd).
    intros P hist s₀ h. apply h.
  Defined.

  Definition histᴰ : D history histᵂ.
  Proof.
    exists histᴹ.
    intros P hist s₀ h. apply h.
  Defined.

  (** pre and post combinator

    Note: we do not need the resp_eutt for post, the generated pre will
    already take care of it.

  *)

  Definition prepostᵂ' [A] (pre : preᵂ) (post : history → run A → Prop) : W' A :=
    λ P hist s₀, pre hist s₀ ∧ (∀ r, post hist r → val P r).

  #[export] Instance prepostᵂ_ismono [A] pre post :
    Monotonous (@prepostᵂ' A pre post).
  Proof.
    intros P Q hPQ hist s₀ h.
    destruct h as [hpre hpost].
    split.
    - assumption.
    - intros r h.
      apply hPQ. apply hpost. assumption.
  Qed.

  Definition prepostᵂ [A] pre post :=
    as_wp (@prepostᵂ' A pre post).

  Lemma prepostᵂ_mono :
    ∀ A (p p' : preᵂ) (q q' : history → run A → Prop),
      (∀ hist s₀, p' hist s₀ → p hist s₀) →
      (∀ hist r, q hist r → q' hist r) →
      prepostᵂ p q ≤ᵂ prepostᵂ p' q'.
  Proof.
    intros A p p' q q' hp hq.
    intros post hist s₀ h.
    destruct h as [hp' hq'].
    split.
    - apply hp. apply hp'.
    - intros r hr. apply hq'. apply hq. apply hr.
  Qed.

  (** Some invariant testing *)

  (* Case: the body always terminates to some inl *)

  Definition always_continuesᵂ [J A] (pre : J → preᵂ) (inv : trace → Prop) (i : J) : W (J + A) :=
    prepostᵂ (pre i) (λ hist r,
      match r with
      | cnv tr s (inl j) => pre j (rev_append (to_trace tr) hist) s ∧ inv (to_trace tr)
      | _ => False
      end
    ).

  Definition inv_loopᵂ [J A] (pre : J → preᵂ) (inv : trace → Prop) (i : J) : W A :=
    prepostᵂ (pre i) (λ hist r,
      match r with
      | div st => ∃ (trs : nat → trace), (∀ n, inv (trs n)) ∧ st ⊑ trs
      | _ => False
      end
    ).

  Lemma always_continues_aux :
    ∀ (tr : otrace) (st : sotrace) (s : nat → trace),
      st ⊑ s →
      stream_prepend tr (stream_prepend [None] st) ⊑
      stream_prepend [to_trace tr] s.
  Proof.
    intros tr st s h. intros n.
    destruct (dec_le n (length tr)) as [hn | hn].
    - exists (length tr), 1.
      split. 1: assumption.
      unfold ttrunc. simpl.
      rewrite strunc_stream_prepend_ge. 2: lia.
      replace (length tr - length tr) with 0 by lia.
      simpl. rewrite !app_nil_r.
      reflexivity.
    - specialize (h (n - length tr)). destruct h as [m [k [hm e]]].
      exists ((S m) + length tr), (S k).
      split. 1: lia.
      rewrite strunc_stream_prepend_ge. 2: lia.
      replace (S m + length tr - length tr) with (S m) by lia.
      unfold ttrunc. simpl.
      rewrite to_trace_app. f_equal.
      simpl. apply e.
  Qed.

  Lemma always_continues :
    ∀ J A pre inv i,
      @iterᵂ J A (always_continuesᵂ pre inv) i ≤ᵂ inv_loopᵂ pre inv i.
  Proof.
    intros J A pre inv i.
    eapply iterᵂ_coind with (w' := λ j, inv_loopᵂ pre inv j).
    clear. intros j. intros post hist s₀ h.
    simpl. red.
    simpl in h. red in h.
    destruct h as [hpre hpost].
    split. 1: assumption.
    intros [t s [i | x] | s]. 2,3: contradiction.
    intros [hi hinv].
    simpl. red.
    split. 1: assumption.
    intros [| st]. 1: contradiction.
    intros [trs [htrs hs]].
    simpl. eapply hpost.
    exists (stream_prepend [to_trace t] trs). split.
    - intros [| n]. all: simpl. all: eauto.
    - apply always_continues_aux. assumption.
  Qed.

  (* Itree interpretation *)
  Import ITree ITreeFacts ITreeNotations.

  Variant ieff : Type → Type :=
  | i_req (p : Prop) : ieff p
  | i_get : ieff state
  | i_put (s : state) : ieff unit
  | i_open (p : path) : ieff file_descr
  | i_read (f : file_descr) : ieff file_content
  | i_close (f : file_descr) : ieff unit
  | i_hist : ieff history.

  Fixpoint toitree [A] (c : M A) : itree ieff A :=
    match c with
    | retᴹ x => Ret x
    | act_reqᴹ p k => x <- trigger (i_req p) ;; toitree (k x)
    | act_iterᴹ J B g i k => x <- iter (1 := Iter_Kleisli) (λ j, toitree (g j)) i ;; toitree (k x)
    | act_getᴹ k => x <- trigger i_get ;; toitree (k x)
    | act_putᴹ s k => trigger (i_put s) ;; toitree k
    | act_openᴹ fp k => x <- trigger (i_open fp) ;; toitree (k x)
    | act_readᴹ fd k => x <- trigger (i_read fd) ;; toitree (k x)
    | act_closeᴹ fd k => trigger (i_close fd) ;; toitree k
    | act_histᴹ k => x <- trigger i_hist ;; toitree (k x)
    end.

End IIOStDiv.
