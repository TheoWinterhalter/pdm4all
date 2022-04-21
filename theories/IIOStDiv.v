(*** Non-termination with instrumented I/O and state

  The partial Dijstra Monad comes with a computation monad that is essentially
  a syntax monad (using a free monad) and the specification gives meaning to
  the different operations, including the iteration operator.

  For I/O we assume we can open and close files as well as read them.
  Because I/O is instrumented we can also read the history up to now.

*)

From Coq Require Import Utf8 RelationClasses List PropExtensionality
  FunctionalExtensionality Arith Lia.
From PDM Require Import util structures guarded PURE.
From PDM Require PDM.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

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

  (* An strace refining a stream of traces *)
  Definition trace_refine (t : strace) (s : nat → trace) : Prop :=
    match t with
    | fintrace t => ∃ n, ∀ m, n ≤ m → t = ttrunc s m
    | inftrace t => ∀ n, ∃ m k, n ≤ m ∧ strunc t m = ttrunc s k
    end.

  Notation "t ⊑ s" := (trace_refine t s) (at level 80).

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

  Lemma trace_refine_prepend :
    ∀ (tr : trace) (st : strace) (s : nat → trace),
      st ⊑ s →
      strace_prepend tr st ⊑ stream_prepend [tr] s.
  Proof.
    intros tr st s h.
    destruct st as [t | t].
    - destruct h as [n h].
      exists (S n). intros m hm.
      destruct m as [| m]. 1: lia.
      rewrite (h m). 2: lia.
      reflexivity.
    - intros n. simpl in h.
      destruct (dec_le n (length tr)) as [hn | hn].
      + exists (length tr), 1.
        split. 1: assumption.
        unfold ttrunc. simpl.
        rewrite strunc_stream_prepend_ge. 2: lia.
        replace (length tr - length tr) with 0 by lia.
        reflexivity.
      + specialize (h (n - length tr)). destruct h as [m [k [hm e]]].
        exists (m + length tr), (S k).
        split. 1: lia.
        unfold ttrunc. simpl.
        rewrite strunc_stream_prepend_ge. 2: lia.
        f_equal. replace (m + length tr - length tr) with m by lia.
        apply e.
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
  Inductive orun A :=
  | ocnv (t : otrace) (s : state) (x : A)
  | odiv (s : sotrace).

  Arguments ocnv [_].
  Arguments odiv [_].

  (* Equal up to tau *)
  Definition eutt [A] (r r' : orun A) : Prop :=
    match r, r' with
    | ocnv t s x, ocnv t' s' x' =>
      to_trace t = to_trace t' ∧ s = s' ∧ x = x'
    | odiv s, odiv s' =>
      uptotau s s'
    | _, _ => False
    end.

  Notation "u ≈ v" := (eutt u v) (at level 80).

  Lemma eutt_refl :
    ∀ A (r : orun A),
      r ≈ r.
  Proof.
    intros A r.
    destruct r.
    - simpl. intuition reflexivity.
    - simpl. apply uptotau_refl.
  Qed.

  Definition resp_eutt [A] (p : orun A → Prop) : Prop :=
    ∀ r r', r ≈ r' → p r → p r'.

  Definition preᴵ :=
    history → state → Prop.

  Definition postᴵ A :=
    { post : orun A → Prop | resp_eutt post }.

  Definition Wᴵ' A := postᴵ A → preᴵ.

  Class Monotonousᴵ [A] (w : Wᴵ' A) :=
    ismonoᴵ :
      ∀ (P Q : postᴵ A),
        (∀ x, val P x → val Q x) →
        ∀ hist s₀, w P hist s₀ → w Q hist s₀.

  Definition Wᴵ A := { w : Wᴵ' A | Monotonousᴵ w }.

  Definition as_wpᴵ [A] (w : Wᴵ' A) {h : Monotonousᴵ w} : Wᴵ A :=
    exist _ w h.

  Instance Monotonousᴵ_val [A] (w : Wᴵ A) : Monotonousᴵ (val w).
  Proof.
    destruct w. assumption.
  Qed.

  Definition retᴵ' [A] (x : A) : Wᴵ' A :=
    λ P hist s₀, val P (ocnv [] s₀ x).

  #[export] Instance retᴵ_ismono [A] (x : A) : Monotonousᴵ (retᴵ' x).
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. apply h.
  Qed.

  Definition retᴵ [A] (x : A) : Wᴵ A :=
    as_wpᴵ (retᴵ' x).

  #[tactic=idtac] Equations? shift_postᴵ [A] (tr : otrace) (P : postᴵ A) : postᴵ A :=
    shift_postᴵ tr P :=
      ⟨ λ r,
          match r with
          | ocnv tr' s x => val P (ocnv (tr ++ tr') s x)
          | odiv st => val P (odiv (stream_prepend tr st))
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

  Lemma shift_postᴵ_nil :
    ∀ A (P : postᴵ A) r,
      val (shift_postᴵ [] P) r → val P r.
  Proof.
    intros A P r h.
    destruct r. all: assumption.
  Qed.

  #[tactic=idtac] Equations? bindᴵ' [A B] (w : Wᴵ A) (wf : A → Wᴵ B) : Wᴵ' B :=
    bindᴵ' w wf :=
      λ P hist s₀,
        val w ⟨ λ r,
          match r with
          | ocnv tr s₁ x => val (wf x) (shift_postᴵ tr P) (rev_append (to_trace tr) hist) s₁
          | odiv s => val P (odiv s)
          end
        ⟩ hist s₀.
  Proof.
    intros r r' h hp.
    destruct P as [P hP].
    destruct r as [t s x | s], r' as [t' s' x' | s']. 2,3: contradiction.
    - simpl in h. destruct h as [et [es ex]]. subst.
      rewrite <- et. eapply ismonoᴵ. 2: eassumption.
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

  #[export] Instance bindᴵ_ismono [A B] (w : Wᴵ A) (wf : A → Wᴵ B) :
    Monotonousᴵ (bindᴵ' w wf).
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

  Definition bindᴵ [A B] (w : Wᴵ A) (wf : A → Wᴵ B) : Wᴵ B :=
    as_wpᴵ (bindᴵ' w wf).

  Definition reqᴵ' (p : Prop) : Wᴵ' p :=
    λ P hist s₀, ∃ (h : p), val P (ocnv [] s₀ h).

  #[export] Instance reqᴵ_ismono : ∀ p, Monotonousᴵ (reqᴵ' p).
  Proof.
    intros p. intros P Q hPQ hist s₀ h.
    destruct h as [hp h].
    exists hp. apply hPQ. assumption.
  Qed.

  Definition reqᴵ (p : Prop) : Wᴵ p :=
    as_wpᴵ (reqᴵ' p).

  Definition tauᴵ' : Wᴵ' unit :=
    λ P hist s₀, val P (ocnv [ None ] s₀ tt).

  #[export] Instance tauᴵ_ismono : Monotonousᴵ tauᴵ'.
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. assumption.
  Qed.

  Definition tauᴵ : Wᴵ unit :=
    as_wpᴵ tauᴵ'.

  Definition getᴵ' : Wᴵ' state :=
    λ P hist s, val P (ocnv [] s s).

  Instance getᴵ_ismono : Monotonousᴵ getᴵ'.
  Proof.
    intros P Q hPQ hist s₀ h.
    red. red in h.
    apply hPQ. assumption.
  Qed.

  Definition getᴵ : Wᴵ state :=
    as_wpᴵ getᴵ'.

  Definition putᴵ' (s : state) : Wᴵ' unit :=
    λ P hist s₀, val P (ocnv [] s tt).

  Instance putᴵ_ismono : ∀ s, Monotonousᴵ (putᴵ' s).
  Proof.
    intros s. intros P Q hPQ hist s₀ h.
    apply hPQ. assumption.
  Qed.

  Definition putᴵ (s : state) : Wᴵ unit :=
    as_wpᴵ (putᴵ' s).

  Definition openᴵ' (fp : path) : Wᴵ' file_descr :=
    λ P hist s₀, ∀ fd, val P (ocnv [ Some (EOpen fp fd) ] s₀ fd).

  Instance openᴵ_ismono : ∀ fp, Monotonousᴵ (openᴵ' fp).
  Proof.
    intros fp. intros P Q hPQ hist s₀ h.
    intro fd.
    apply hPQ. apply h.
  Qed.

  Definition openᴵ (fp : path) : Wᴵ file_descr :=
    as_wpᴵ (openᴵ' fp).

  Definition readᴵ' (fd : file_descr) : Wᴵ' file_content :=
    λ P hist s₀, is_open fd hist ∧ ∀ fc, val P (ocnv [ Some (ERead fd fc) ] s₀ fc).

  Instance readᴵ_ismono : ∀ fd, Monotonousᴵ (readᴵ' fd).
  Proof.
    intros fd. intros P Q hPQ hist s₀ h.
    destruct h as [ho h].
    split.
    - assumption.
    - intro fc. apply hPQ. apply h.
  Qed.

  Definition readᴵ (fd : file_descr) : Wᴵ file_content :=
    as_wpᴵ (readᴵ' fd).

  Definition closeᴵ' (fd : file_descr) : Wᴵ' unit :=
    λ P hist s₀, is_open fd hist ∧ val P (ocnv [ Some (EClose fd) ] s₀ tt).

  Instance closeᴵ_ismono : ∀ fd, Monotonousᴵ (closeᴵ' fd).
  Proof.
    intros fd. intros P Q hPQ hist s₀ h.
    destruct h as [ho h].
    split.
    - assumption.
    - apply hPQ. assumption.
  Qed.

  Definition closeᴵ (fd : file_descr) : Wᴵ unit :=
    as_wpᴵ (closeᴵ' fd).

  Definition histᴵ' : Wᴵ' history :=
    λ P hist s₀, val P (ocnv [] s₀ hist).

  Instance histᴵ_ismono : Monotonousᴵ histᴵ'.
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. assumption.
  Qed.

  Definition histᴵ : Wᴵ history :=
    as_wpᴵ histᴵ'.

  #[export] Instance Monad_Wᴵ : Monad Wᴵ := {|
    ret := retᴵ ;
    bind := bindᴵ
  |}.

  #[export] Instance ReqMonad_Wᴵ : ReqMonad Wᴵ := {|
    req := reqᴵ
  |}.

  Definition wleᴵ [A] (w₀ w₁ : Wᴵ A) : Prop :=
    ∀ P hist s₀, val w₁ P hist s₀ → val w₀ P hist s₀.

  #[export] Instance Order_Wᴵ : Order Wᴵ.
  Proof.
    exists wleᴵ.
    intros A x y z h₁ h₂. intros P hist s₀ h.
    apply h₁. apply h₂.
    assumption.
  Defined.

  #[export] Instance Reflexive_wleᴵ [A] : Reflexive (wleᴵ (A := A)).
  Proof.
    intro w. intros p hist s₀ h. assumption.
  Qed.

  #[export] Instance MonoSpec_Wᴵ : MonoSpec Wᴵ.
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

  (* Specification of iter using an impredicative encoding *)
  Definition iter_expand [J A] (w : J → Wᴵ (J + A)) (i : J) (k : J → Wᴵ A) : Wᴵ A :=
    bind (w i) (λ x,
      match x with
      | inl j => bind tauᴵ (λ _, k j)
      | inr y => ret y
      end
    ).

  Lemma iter_expand_mono :
    ∀ J A (w w' : J → Wᴵ (J + A)) (i : J) (k : J → Wᴵ A),
      w i ≤ᵂ w' i →
      iter_expand w i k ≤ᵂ iter_expand w' i k.
  Proof.
    intros J A w w' i k hw.
    unfold iter_expand. eapply bind_mono.
    - apply hw.
    - intro. reflexivity.
  Qed.

  (* Greatest fixpoint of [iter_expand w j (iterᵂ' w) ≤ᵂ iterᵂ' w j] *)
  Definition iterᴵ' [J A] (w : J → Wᴵ (J + A)) (i : J) : Wᴵ' A :=
    λ post hist s₀,
      ∃ (P : J → Wᴵ A),
        (∀ j, iter_expand w j P ≤ᵂ P j) ∧
        val (P i) post hist s₀.

  #[export] Instance iterᴵ_ismono [J A] (w : J → Wᴵ (J + A)) (i : J) :
    Monotonousᴵ (iterᴵ' w i).
  Proof.
    intros P Q hPQ hist s₀ h.
    destruct h as [iᵂ [helim hi]].
    exists iᵂ. split.
    - apply helim.
    - eapply ismonoᴵ.
      + eapply hPQ.
      + assumption.
  Qed.

  Definition iterᴵ [J A] w i :=
    as_wpᴵ (@iterᴵ' J A w i).

  Lemma iterᴵ_unfold :
    ∀ J A (w : J → Wᴵ (J + A)) (i : J),
      iter_expand w i (iterᴵ w) ≤ᵂ iterᴵ w i.
  Proof.
    intros J A w i. intros post hist s₀ h.
    destruct h as [iᵂ [helim hi]].
    eapply helim in hi as h. simpl in h. red in h.
    simpl. red. eapply ismonoᴵ. 2: exact h.
    simpl. intros [tr s₁ [j | x] | st] hh.
    - simpl. red.
      exists iᵂ. split. all: auto.
    - assumption.
    - assumption.
  Qed.

  Lemma iterᴵ_coind :
    ∀ J A (w : J → Wᴵ (J + A)) (i : J) (w' : J → Wᴵ A),
      (∀ j, iter_expand w j w' ≤ᵂ w' j) →
      iterᴵ w i ≤ᵂ w' i.
  Proof.
    intros J A w i w' h.
    intros post hist s₀ h'.
    exists w'. split. all: assumption.
  Qed.

  Lemma iterᴵ_fold :
    ∀ J A (w : J → Wᴵ (J + A)) (i : J),
    iterᴵ w i ≤ᵂ iter_expand w i (iterᴵ w).
  Proof.
    intros J A w i.
    eapply iterᴵ_coind with (w' := λ i, iter_expand _ i _). clear i.
    intros i.
    eapply bind_mono. 1: reflexivity.
    intros [].
    - eapply bind_mono. 1: reflexivity.
      intros _. apply iterᴵ_unfold.
    - reflexivity.
  Qed.

  Definition liftᴵ [A] (w : pure_wp A) : Wᴵ A.
  Proof.
    exists (λ P hist s₀, val w (λ x, val P (ocnv [] s₀ x))).
    intros P Q hPQ hist s₀ h.
    destruct w as [w mw].
    eapply mw. 2: exact h.
    simpl. intros x. apply hPQ.
  Defined.

  #[export] Instance hliftᴵ : PureSpec Wᴵ Order_Wᴵ liftᴵ.
  Proof.
    constructor.
    intros A w f.
    intros P hist s₀ h.
    assert (hpre : val w (λ _, True)).
    { unfold liftᴵ in h.
      destruct w as [w hw].
      eapply hw. 2: exact h.
      auto.
    }
    cbv. exists hpre.
    pose proof (prf (f hpre)) as hf. simpl in hf.
    apply hf in h. assumption.
  Qed.

  (* Effect observation *)

  Fixpoint θᴵ [A] (c : M A) : Wᴵ A :=
    match c with
    | retᴹ x => ret x
    | act_getᴹ k => bind getᴵ (λ x, θᴵ (k x))
    | act_putᴹ s k => bind (putᴵ s) (λ _, θᴵ k)
    | act_reqᴹ p k => bind (reqᴵ p) (λ x, θᴵ (k x))
    | act_iterᴹ J B g i k => bind (iterᴵ (λ i, θᴵ (g i)) i) (λ x, θᴵ (k x))
    | act_openᴹ fp k => bind (openᴵ fp) (λ x, θᴵ (k x))
    | act_readᴹ fd k => bind (readᴵ fd) (λ x, θᴵ (k x))
    | act_closeᴹ fd k => bind (closeᴵ fd) (λ x, θᴵ k)
    | act_histᴹ k => bind histᴵ (λ x, θᴵ (k x))
    end.

  Lemma bindᴵ_assoc :
    ∀ A B C (w : Wᴵ A) (wf : A → Wᴵ B) (wg : B → Wᴵ C),
      bind w (λ x, bind (wf x) wg) ≤ᵂ bind (bind w wf) wg.
  Proof.
    intros A B C w wf wg.
    intros P hist s₀ h.
    simpl. red.
    simpl in h. red in h.
    eapply ismonoᴵ. 2: exact h.
    simpl. intros [].
    - intro hf. red.
      eapply ismonoᴵ. 2: exact hf.
      simpl. intros [].
      + rewrite !rev_append_rev. rewrite to_trace_app.
        rewrite rev_app_distr. rewrite !app_assoc.
        intro hg.
        eapply ismonoᴵ. 2: exact hg.
        intros [].
        * simpl. rewrite app_assoc. auto.
        * simpl. rewrite stream_prepend_app. auto.
      + auto.
    - auto.
  Qed.

  Instance θᴵ_lax : LaxMorphism θᴵ.
  Proof.
    constructor.
    - intros A x.
      reflexivity.
    - intros A B c f.
      induction c
      as [ A x | A p k ih | A J C g ihg i k ih | A k ih | A p k ih | A fp k ih | A fd k ih | A fd k ih | A k ih]
      in B, f |- *.
      2-9: cbn - [wle bind].
      2-9: etransitivity ; [| eapply bindᴵ_assoc].
      2-9: cbn - [wle].
      2-9: change bindᴵ with bind.
      2-9: eapply bind_mono ; [reflexivity |].
      2-9: intro.
      2-9: apply ih.
      intros P hist s₀ h.
      simpl. simpl in h.
      eapply ismonoᴵ. 2: exact h.
      apply shift_postᴵ_nil.
  Qed.

  Instance θᴵ_reqlax : ReqLaxMorphism _ θᴵ.
  Proof.
    constructor.
    intros p. intros post hist s₀ h.
    simpl. red. simpl.
    simpl in h. red in h.
    destruct h as [hp h]. exists hp. assumption.
  Qed.

  (* Final specification monad *)

  (* TODO: Can we do something interesting about state in infinite branches? *)
  Inductive run A :=
  | cnv (t : trace) (s : state) (x : A)
  | div (s : strace).

  Arguments cnv [_].
  Arguments div [_].

  Definition preᵂ := history → state → Prop.
  Definition postᵂ A := run A → Prop.

  Definition W' A := postᵂ A → preᵂ.

  Class Monotonous [A] (w : W' A) :=
    ismono :
      ∀ (P Q : postᵂ A),
        (∀ x, P x → Q x) →
        ∀ hist s₀, w P hist s₀ → w Q hist s₀.

  Definition W A := { w : W' A | Monotonous w }.

  Definition as_wp [A] (w : W' A) {h : Monotonous w} : W A :=
    exist _ w h.

  Instance Monotonous_val [A] (w : W A) : Monotonous (val w).
  Proof.
    destruct w. assumption.
  Qed.

  Definition retᵂ' [A] (x : A) : W' A :=
    λ P hist s₀, P (cnv [] s₀ x).

  #[export] Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ' x).
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. apply h.
  Qed.

  Definition retᵂ [A] (x : A) : W A :=
    as_wp (retᵂ' x).

  Definition shift_post [A] (tr : trace) (P : postᵂ A) : postᵂ A :=
    λ r,
      match r with
      | cnv tr' s x => P (cnv (tr ++ tr') s x)
      | div st => P (div (strace_prepend tr st))
      end.

  Definition bindᵂ' [A B] (w : W A) (wf : A → W B) : W' B :=
    λ P hist s₀,
      val w (λ r,
        match r with
        | cnv tr s₁ x => val (wf x) (shift_post tr P) (rev_append tr hist) s₁
        | div s => P (div s)
        end
      ) hist s₀.

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
    λ P hist s₀, ∃ (h : p), P (cnv [] s₀ h).

  #[export] Instance reqᵂ_ismono : ∀ p, Monotonous (reqᵂ' p).
  Proof.
    intros p. intros P Q hPQ hist s₀ h.
    destruct h as [hp h].
    exists hp. apply hPQ. assumption.
  Qed.

  Definition reqᵂ (p : Prop) : W p :=
    as_wp (reqᵂ' p).

  Definition getᵂ' : W' state :=
    λ P hist s, P (cnv [] s s).

  Instance getᵂ_ismono : Monotonous getᵂ'.
  Proof.
    intros P Q hPQ hist s₀ h.
    red. red in h.
    apply hPQ. assumption.
  Qed.

  Definition getᵂ : W state :=
    as_wp getᵂ'.

  Definition putᵂ' (s : state) : W' unit :=
    λ P hist s₀, P (cnv [] s tt).

  Instance putᵂ_ismono : ∀ s, Monotonous (putᵂ' s).
  Proof.
    intros s. intros P Q hPQ hist s₀ h.
    apply hPQ. assumption.
  Qed.

  Definition putᵂ (s : state) : W unit :=
    as_wp (putᵂ' s).

  Definition openᵂ' (fp : path) : W' file_descr :=
    λ P hist s₀, ∀ fd, P (cnv [ EOpen fp fd ] s₀ fd).

  Instance openᵂ_ismono : ∀ fp, Monotonous (openᵂ' fp).
  Proof.
    intros fp. intros P Q hPQ hist s₀ h.
    intro fd.
    apply hPQ. apply h.
  Qed.

  Definition openᵂ (fp : path) : W file_descr :=
    as_wp (openᵂ' fp).

  Definition readᵂ' (fd : file_descr) : W' file_content :=
    λ P hist s₀, is_open fd hist ∧ ∀ fc, P (cnv [ ERead fd fc ] s₀ fc).

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
    λ P hist s₀, is_open fd hist ∧ P (cnv [ EClose fd ] s₀ tt).

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
    λ P hist s₀, P (cnv [] s₀ hist).

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

  #[export] Instance WOrder : Order W.
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

  #[export] Instance WMono : MonoSpec W.
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

  (* Connection between W and Wᴵ *)

  Definition refine_run [A] (r : run A) (r' : orun A) :=
    match r, r' with
    | cnv t s x, ocnv t' s' x' => t = to_trace t' ∧ s = s' ∧ x = x'
    | div s, odiv s' => s ⊆ s'
    | _, _ => False
    end.

  (* TODO MOVE *)
  Lemma strunc_ge :
    ∀ A (s : nat → A) n m,
      n ≤ m →
      strunc s m = strunc s n ++ skipn n (strunc s m).
  Proof.
    intros A s n m h.
    induction m as [| m ih] in n, s, h |- *.
    - simpl. rewrite skipn_nil.
      assert (n = 0) by lia. subst.
      reflexivity.
    - simpl. destruct n.
      + simpl. reflexivity.
      + simpl. f_equal. apply ih. lia.
  Qed.

  (* TODO MOVE *)
  Lemma app_id_inv :
    ∀ A (l l' : list A),
      l ++ l' = l →
      l' = [].
  Proof.
    intros A l l' e.
    induction l as [| a l ih] in l', e |- *.
    - assumption.
    - apply ih. simpl in e. noconf e. assumption.
  Qed.

  Lemma uptotau_sotrace_refine :
    ∀ s₁ s₂ s,
      uptotau s₁ s₂ →
      s ⊆ s₂ →
      s ⊆ s₁.
  Proof.
    intros s₁ s₂ s [es₁ es₂] h.
    unfold embeds in *.
    destruct s.
    - simpl in *. destruct h as [n h].
      specialize (h n) as hn. forward hn by lia. subst.
      specialize (es₁ n) as esn. destruct esn as [n' h'].
      exists n'. intros m hm.
      specialize (es₂ m) as esm. destruct esm as [m' hm'].
      destruct (dec_le n m') as [hn | hn].
      + rewrite hm'. apply h. assumption.
      + rewrite strunc_ge with (n := m') in h'. 2: lia.
        rewrite to_trace_app in h'.
        erewrite strunc_ge in hm'. 2: eassumption.
        rewrite to_trace_app in hm'. rewrite <- h' in hm'.
        rewrite <- !app_assoc in hm'.
        apply app_id_inv in hm'. apply app_eq_nil in hm'.
        destruct hm' as [e1 e2].
        rewrite strunc_ge with (n := m'). 2: lia.
        symmetry.
        erewrite strunc_ge. 2: eassumption.
        rewrite !to_trace_app. rewrite e1, e2.
        rewrite e1 in h'. rewrite h'. apply app_nil_r.
    - simpl in *. intros n.
      specialize (h n). destruct h as [m h].
      specialize (es₁ m). destruct es₁ as [k e].
      exists k. rewrite h. assumption.
  Qed.

  Lemma eutt_refine_run :
    ∀ A r₁ r₂ (r : run A),
      r₁ ≈ r₂ →
      refine_run r r₂ →
      refine_run r r₁.
  Proof.
    intros A r₁ r₂ r er h.
    destruct r₁, r₂. 2,3: contradiction.
    - destruct r. 2: contradiction.
      simpl in *. intuition subst. all: eauto.
    - destruct r. 1: contradiction.
      simpl in *. eapply uptotau_sotrace_refine. all: eassumption.
  Qed.

  #[tactic=idtac] Equations? fromᴵ' [A] (wᴵ : Wᴵ A) : W' A :=
    fromᴵ' wᴵ :=
      λ P hist s₀, val wᴵ ⟨ λ r', ∀ r, refine_run r r' → P r ⟩ hist s₀.
  Proof.
    intros r₁ r₂ er h. intros r hr.
    apply h. eapply eutt_refine_run. all: eassumption.
  Qed.

  Instance fromᴵ_ismono [A] (wᴵ : Wᴵ A) : Monotonous (fromᴵ' wᴵ).
  Proof.
    intros P Q hPQ hist s₀ h.
    red. red in h.
    eapply ismonoᴵ. 2: exact h.
    simpl. intros r' hP r hr.
    apply hPQ. apply hP. assumption.
  Qed.

  Definition fromᴵ [A] (wᴵ : Wᴵ A) : W A :=
    as_wp (fromᴵ' wᴵ).

  Lemma fromᴵ_mono :
    ∀ A (w w' : Wᴵ A),
      w ≤ᵂ w' →
      fromᴵ w ≤ᵂ fromᴵ w'.
  Proof.
    intros A w w' hw.
    intros P hist s₀ h.
    simpl. red. simpl in h. red in h.
    eapply hw. assumption.
  Qed.

  Definition toᴵ' [A] (w : W A) : Wᴵ' A :=
    λ P hist s₀, val w (λ r, ∀ r', refine_run r r' → val P r') hist s₀.

  Instance toᴵ_ismono [A] (w : W A) : Monotonousᴵ (toᴵ' w).
  Proof.
    intros P Q hPQ hist s₀ h.
    red. red in h.
    eapply ismono. 2: exact h.
    simpl. intros r hP r' hr.
    apply hPQ. apply hP. assumption.
  Qed.

  Definition toᴵ [A] (w : W A) : Wᴵ A :=
    as_wpᴵ (toᴵ' w).

  Lemma toᴵ_mono :
    ∀ A (w w' : W A),
      w ≤ᵂ w' →
      toᴵ w ≤ᵂ toᴵ w'.
  Proof.
    intros A w w' hw.
    intros P hist s₀ h.
    simpl. red. simpl in h. red in h.
    eapply hw. assumption.
  Qed.

  Definition iterᵂ [J A] (w : J → W (J + A)) (i : J) : W A :=
    fromᴵ (iterᴵ (λ j, toᴵ (w j)) i).

  (** Dijstra monad in the style of DM4ever *)

  Definition Dᴵ A w : Type :=
    PDM.D (θ := θᴵ) A w.

  Instance DijkstraMonad_Dᴵ : DijkstraMonad Dᴵ :=
    PDM.DijkstraMonad_D MonoSpec_Wᴵ θᴵ_lax.

  (* Lift from PURE *)

  Definition liftᴾᴵ : ∀ A w, PURE A w → Dᴵ A (liftᴵ w) :=
    PDM.liftᴾ (M := M) (W := Wᴵ) MonoSpec_Wᴵ θᴵ_lax θᴵ_reqlax hliftᴵ.

  (* Actions *)

  Definition iterᴰᴵ [J A w] (f : ∀ (j : J), Dᴵ (J + A) (w j)) i : Dᴵ A (iterᴵ w i).
  Proof.
    exists (iterᴹ (λ j, val (f j)) i).
    intros P hist s₀ h.
    simpl. simpl in h.
    destruct h as [iᵂ [helim hi]].
    exists iᵂ. split.
    - intros j. etransitivity. 2: eapply helim.
      apply iter_expand_mono.
      eapply prf.
    - eapply ismonoᴵ. 2: exact hi.
      intros [].
      + rewrite app_nil_r. auto.
      + auto.
  Defined.

  (** Dijstra monad without taus *)

  Definition θ [A] (c : M A) : W A :=
    fromᴵ (θᴵ c).

  (* TODO MOVE *)
  Lemma length_to_trace :
    ∀ t,
      length (to_trace t) ≤ length t.
  Proof.
    intro t.
    induction t as [| [e |] t ih].
    - auto.
    - simpl. lia.
    - simpl. lia.
  Qed.

  (* TODO MOVE *)
  Lemma strunc_stream_skip :
    ∀ A (s : nat → A) n m,
      strunc (stream_skipn s n) m = skipn n (strunc s (n + m)).
  Proof.
    intros A s n m.
    induction n as [| n ih] in m, s |- *.
    - simpl. reflexivity.
    - simpl. rewrite <- ih. reflexivity.
  Qed.

  Lemma firstn_to_trace_strunc :
    ∀ s n k,
      ∃ m, firstn n (to_trace (strunc s k)) = to_trace (strunc s m).
  Proof.
    intros s n k.
    induction n as [| n ih] in k, s |- *.
    - simpl. exists 0. reflexivity.
    - induction k as [| k ihk] in s |- *.
      + simpl. exists 0. reflexivity.
      + simpl to_trace. destruct (s 0) eqn:e.
        * simpl. specialize (ih (λ p, s (S p)) k). destruct ih as [m h].
          rewrite h.
          exists (S m). simpl. rewrite e. reflexivity.
        * specialize (ihk (λ p, s (S p))). destruct ihk as [m h].
          rewrite h.
          exists (S m). simpl. rewrite e. reflexivity.
  Qed.

  (* TODO MOVE *)
  Lemma sotrace_refine_prepend_inv :
    ∀ st t s,
      st ⊆ stream_prepend t s →
      ∃ st', st = strace_prepend (to_trace t) st' ∧ st' ⊆ s.
  Proof.
    intros st t s h.
    destruct st as [t' | t'].
    - simpl in h. destruct h as [n h].
      exists (fintrace (skipn (length (to_trace t)) t')).
      split.
      + simpl. specialize (h (n + length t)) as e.
        forward e by lia. subst. f_equal.
        rewrite strunc_stream_prepend_ge. 2: lia.
        rewrite to_trace_app. f_equal.
        rewrite skipn_app. rewrite skipn_all. simpl.
        replace (length (to_trace t) - length (to_trace t)) with 0 by lia.
        rewrite skipn_O. reflexivity.
      + simpl. exists n.
        intros m hm.
        specialize (h (m + length t)). forward h by lia. subst.
        rewrite strunc_stream_prepend_ge. 2: lia.
        rewrite to_trace_app.
        rewrite skipn_app. rewrite skipn_all. simpl.
        replace (length (to_trace t) - length (to_trace t)) with 0 by lia.
        rewrite skipn_O. f_equal. f_equal. lia.
    - simpl in h.
      specialize (h (length t)) as e.
      destruct e as [m e]. apply (f_equal (λ l, length l)) in e as e'.
      rewrite strunc_length in e'.
      pose proof (length_to_trace (strunc (stream_prepend t s) m)) as ht.
      rewrite strunc_length in ht. rewrite <- e' in ht.
      rewrite strunc_stream_prepend_ge in e. 2: lia.
      rewrite to_trace_app in e.
      clear e'. apply (f_equal (firstn (length (to_trace t)))) in e as e'.
      rewrite strunc_ge with (n := length (to_trace t)) in e'.
      2: apply length_to_trace.
      rewrite firstn_app in e'.
      rewrite firstn_all2 in e'. 2:{ rewrite strunc_length. auto. }
      rewrite strunc_length in e'.
      replace (length (to_trace t) - length (to_trace t)) with 0 in e' by lia.
      simpl in e'. rewrite app_nil_r in e'.
      replace (length (to_trace t)) with (length (to_trace t) + 0) in e' by lia.
      rewrite firstn_app_2 in e'. simpl in e'. rewrite app_nil_r in e'.
      replace (length (to_trace t) + 0) with (length (to_trace t)) in e' by lia.
      exists (inftrace (stream_skipn t' (length (to_trace t)))).
      split.
      + simpl. f_equal.
        rewrite <- e'. rewrite strunc_length.
        rewrite stream_prepend_skipn. reflexivity.
      + simpl. intros n.
        specialize (h (length t + n)). destruct h as [m' h].
        apply (f_equal (λ l, length l)) in h as eh.
        rewrite strunc_length in eh.
        pose proof (length_to_trace (strunc (stream_prepend t s) m')) as eht.
        rewrite strunc_length in eht. rewrite <- eh in eht.
        rewrite strunc_stream_prepend_ge in h. 2: lia.
        rewrite to_trace_app in h.
        apply (f_equal (firstn (length (to_trace t) + n))) in h as h'.
        rewrite strunc_ge with (n := length (to_trace t) + n) in h'.
        2:{ pose proof (length_to_trace t). lia. }
        rewrite firstn_app in h'.
        rewrite firstn_all2 in h'. 2:{ rewrite strunc_length. auto. }
        rewrite strunc_length in h'.
        replace (length (to_trace t) + n - (length (to_trace t) + n)) with 0 in h' by lia.
        simpl in h'. rewrite app_nil_r in h'.
        rewrite firstn_app_2 in h'.
        rewrite strunc_ge with (n := length (to_trace t)) in h'. 2: lia.
        rewrite e' in h'.
        apply app_inv_head in h'.
        rewrite strunc_stream_skip. rewrite h'.
        apply firstn_to_trace_strunc.
  Qed.

  Instance θ_lax : LaxMorphism θ.
  Proof.
    constructor.
    - intros A x.
      unfold θ. etransitivity.
      + eapply fromᴵ_mono. eapply θ_ret.
      + intros P hist s h.
        simpl. simpl in h. red in h.
        intros [] hr. 2: contradiction.
        simpl in hr. intuition subst.
        assumption.
    - intros A B c f.
      unfold θ. etransitivity.
      + eapply fromᴵ_mono. eapply θ_bind.
      + intros P hist s h.
        simpl. red. simpl in h. red in h.
        eapply ismonoᴵ. 2: exact h.
        clear h.
        simpl. intros [t s' x | s'] h.
        * {
          specialize (h (cnv (to_trace t) s' x)).
          forward h.
          { simpl. intuition reflexivity. }
          simpl in h. red in h.
          eapply ismonoᴵ. 2: exact h.
          simpl. clear.
          intros [t' s x | s] h r hr.
          - destruct r. 2: contradiction.
            simpl in hr. intuition subst.
            specialize (h (cnv (to_trace t') s x)).
            forward h.
            { simpl. intuition reflexivity. }
            simpl in h. rewrite to_trace_app. assumption.
          - destruct r as [| st]. 1: contradiction.
            simpl in hr.
            apply sotrace_refine_prepend_inv in hr.
            destruct hr as [st' [? hr]]. subst.
            specialize (h (div st')).
            forward h.
            { simpl. assumption. }
            assumption.
        }
        * intros r hr.
          destruct r as [| st]. 1: contradiction.
          specialize (h (div st)).
          forward h.
          { assumption. }
          simpl in h. assumption.
  Qed.

  Instance θ_reqlax : ReqLaxMorphism _ θ.
  Proof.
    constructor.
    intros p.
    unfold θ. etransitivity.
    - eapply fromᴵ_mono. eapply θ_req.
    - intros post hist s₀ h.
      simpl. red.
      simpl in h. red in h.
      destruct h as [hp h]. exists hp.
      intros r hr.
      destruct r. 2: contradiction.
      simpl in hr. intuition subst.
      assumption.
  Qed.

  Definition D A w : Type :=
    PDM.D (θ := θ) A w.

  Instance DijkstraMonad_D : DijkstraMonad D :=
    PDM.DijkstraMonad_D WMono θ_lax.

  (* Lift from PURE *)

  Definition liftᵂ [A] (w : pure_wp A) : W A.
  Proof.
    exists (λ P hist s₀, val w (λ x, P (cnv [] s₀ x))).
    intros P Q hPQ hist s₀ h.
    destruct w as [w mw].
    eapply mw. 2: exact h.
    simpl. intros x. apply hPQ.
  Defined.

  #[export] Instance hlift : PureSpec W WOrder liftᵂ.
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

  Definition liftᴾ : ∀ A w, PURE A w → D A (liftᵂ w) :=
    PDM.liftᴾ (M := M) (W := W) WMono θ_lax θ_reqlax hlift.

  (* Actions *)

  Definition getᴰ : D state getᵂ.
  Proof.
    exists getᴹ.
    intros P hist s₀ h.
    simpl. simpl in h. red in h.
    intros [] hr. 2: contradiction.
    simpl in hr. intuition subst.
    assumption.
  Defined.

  Definition putᴰ (s : state) : D unit (putᵂ s).
  Proof.
    exists (putᴹ s).
    intros P hist s₀ h.
    simpl. simpl in h. red in h.
    intros [] hr. 2: contradiction.
    simpl in hr. intuition subst.
    assumption.
  Defined.

  Definition openᴰ fp : D file_descr (openᵂ fp).
  Proof.
    exists (openᴹ fp).
    intros P hist s₀ h.
    simpl. red. simpl in h. red in h.
    intros fd [] hr. 2: contradiction.
    simpl in hr. intuition subst.
    apply h.
  Defined.

  Definition readᴰ fd : D file_content (readᵂ fd).
  Proof.
    exists (readᴹ fd).
    intros P hist s₀ h.
    simpl. red. simpl in h. red in h.
    destruct h as [? h].
    split. 1: assumption.
    intros fc [] hr. 2: contradiction.
    simpl in hr. intuition subst.
    apply h.
  Defined.

  Definition closeᴰ fd : D unit (closeᵂ fd).
  Proof.
    exists (closeᴹ fd).
    intros P hist s₀ h.
    simpl. red. simpl in h. red in h.
    destruct h as [? h].
    split. 1: assumption.
    intros [] hr. 2: contradiction.
    simpl in hr. intuition subst.
    apply h.
  Defined.

  Definition histᴰ : D history histᵂ.
  Proof.
    exists histᴹ.
    intros P hist s₀ h.
    simpl. simpl in h. red in h.
    intros [] hr. 2: contradiction.
    simpl in hr. intuition subst.
    apply h.
  Defined.

  (* We could also make this simpler by having a different notion of strace *)
  (* Have to see whether it is worth it. *)
  Lemma sotrace_refine_exists :
    ∀ s, ∃ st, st ⊆ s.
  Proof.
    intros s.
  Admitted.

  Lemma to_fromᴵ :
    ∀ A (w : Wᴵ A),
      w ≤ᵂ toᴵ (fromᴵ w).
  Proof.
    intros A w.
    intros P hsit s₀ h.
    simpl in h. red in h.
    eapply ismonoᴵ. 2: exact h.
    clear. simpl.
    intros [t s x | s] h.
    - eapply h with (r := cnv (to_trace t) s x).
      all: simpl. all: intuition reflexivity.
    - destruct (sotrace_refine_exists s) as [st hs].
      eapply h with (r := div st).
      all: simpl. all: assumption.
  Qed.

  Definition iterᴰ [J A w] (f : ∀ (j : J), D (J + A) (w j)) i :
    D A (iterᵂ w i).
  Proof.
    exists (iterᴹ (λ j, val (f j)) i).
    unfold iterᵂ. eapply fromᴵ_mono.
    intros P hist s₀ h.
    simpl. simpl in h.
    destruct h as [iᵂ [helim hi]].
    exists iᵂ. split.
    - intros j. etransitivity. 2: eapply helim.
      apply iter_expand_mono.
      etransitivity. 1: eapply to_fromᴵ.
      eapply toᴵ_mono. eapply prf.
    - eapply ismonoᴵ. 2: exact hi.
      intros [].
      + rewrite app_nil_r. auto.
      + auto.
  Defined.

  (*

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
      + red. red. rewrite app_nil_r. auto.
      + auto.
  Defined.

  (* pre and post combinator *)

  Definition prepostᵂ' [A] (pre : preᵂ) (post : history → postᵂ A) : W' A :=
    λ P hist s₀, pre hist s₀ ∧ (∀ r, post hist r → P r).

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
    ∀ A (p p' : preᵂ) (q q' : history → postᵂ A),
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
      | cnv tr s (inl j) => pre j (rev_append tr hist) s ∧ inv tr
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

  Lemma always_continues :
    ∀ J A pre inv i,
      @iterᵂ J A (always_continuesᵂ pre inv) i ≤ᵂ inv_loopᵂ pre inv i.
  Proof.
    intros J A pre inv i.
    intros post hist s₀ h.
    eexists. split. 2: eassumption.
    intros j. intros post' hist' s₀' h'.
    simpl in h'. simpl.
    destruct h' as [hpre hpost].
    split.
    - assumption.
    - intros [tr s [k | x] | st] hk. 2,3: contradiction.
      destruct hk as [hk htr].
      split.
      + assumption.
      + intros [| st]. 1: contradiction.
        intros [trs [htrs hst]]. simpl.
        eapply hpost.
        exists (stream_prepend [tr] trs). split.
        * intros [| n]. all: simpl. all: eauto.
        * apply trace_refine_prepend. assumption.
  Qed.

  (* Sadly, the current iterᵂ can prove any spec for a loop. *)
  Lemma always_wrong :
    ∀ J A (i : J) w,
      @iterᵂ J A (λ j, ret (inl j)) i ≤ᵂ w.
  Proof.
    intros J A i w.
    eapply iterᵂ_coind with (w' := λ j, _).
    intros j. intros post hist s₀ h.
    simpl. red.
    rewrite rev_append_rev. simpl.
    eapply ismono. 2: exact h.
    apply shift_post_nil_imp.
  Qed.

  (* Test with another version of iterᵂ with step counting *)

  (* Specification of iter using an impredicative encoding *)
  Definition step_iter_expand [J A] (w : J → W (J + A)) (i : J) (k : J → W (nat * A)) : W (nat * A) :=
    bind (w i) (λ x,
      match x with
      | inl j => bind (k j) (λ '(n, y), ret (S n, y))
      | inr y => ret (0, y)
      end
    ). *)

End IIOStDiv.