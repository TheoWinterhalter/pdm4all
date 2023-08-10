(*** Non-termination with I/O

  Variant of IIOStDiv but without state and monitoring.

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

Section IODiv.

  Context (path file_descr file_content : Type).

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
  | act_openᴹ (p : path) (k : file_descr → M A)
  | act_readᴹ (f : file_descr) (k : file_content → M A)
  | act_closeᴹ (f : file_descr) (k : M A).

  Arguments retᴹ [_].
  Arguments act_reqᴹ [_].
  Arguments act_iterᴹ [_].
  Arguments act_openᴹ [_].
  Arguments act_readᴹ [_].
  Arguments act_closeᴹ [_].

  Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    match c with
    | retᴹ x => f x
    | act_reqᴹ p k => act_reqᴹ p (λ h, bindᴹ (k h) f)
    | act_iterᴹ J B g i k => act_iterᴹ J B g i (λ h, bindᴹ (k h) f)
    | act_openᴹ fp k => act_openᴹ fp (λ x, bindᴹ (k x) f)
    | act_readᴹ fd k => act_readᴹ fd (λ x, bindᴹ (k x) f)
    | act_closeᴹ fd k => act_closeᴹ fd (bindᴹ k f)
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

  Definition openᴹ fp :=
    act_openᴹ fp (λ x, ret x).

  Definition readᴹ fd :=
    act_readᴹ fd (λ x, ret x).

  Definition closeᴹ fd :=
    act_closeᴹ fd (ret tt).

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
  | cnv (t : otrace) (x : A)
  | div (s : sotrace).

  Arguments cnv [_].
  Arguments div [_].

  (* Equal up to tau *)
  Definition eutt [A] (r r' : run A) : Prop :=
    match r, r' with
    | cnv t x, cnv t' x' =>
      to_trace t = to_trace t' ∧ x = x'
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
    history → Prop.

  Definition postᵂ A :=
    { post : run A → Prop | resp_eutt post }.

  Definition W' A := postᵂ A → preᵂ.

  Class Monotonous [A] (w : W' A) :=
    ismono :
      ∀ (P Q : postᵂ A),
        (∀ x, val P x → val Q x) →
        ∀ hist, w P hist → w Q hist.

  Definition W A := { w : W' A | Monotonous w }.

  Definition as_wp [A] (w : W' A) {h : Monotonous w} : W A :=
    exist _ w h.

  Instance Monotonous_val [A] (w : W A) : Monotonous (val w).
  Proof.
    destruct w. assumption.
  Qed.

  Definition retᵂ' [A] (x : A) : W' A :=
    λ P hist, val P (cnv [] x).

  #[export] Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ' x).
  Proof.
    intros P Q hPQ hist h.
    apply hPQ. apply h.
  Qed.

  Definition retᵂ [A] (x : A) : W A :=
    as_wp (retᵂ' x).

  #[tactic=idtac] Equations? shift_post [A] (tr : otrace) (P : postᵂ A) : postᵂ A :=
    shift_post tr P :=
      ⟨ λ r,
          match r with
          | cnv tr' x => val P (cnv (tr ++ tr') x)
          | div st => val P (div (stream_prepend tr st))
          end
      ⟩.
  Proof.
    intros r r' h hp.
    destruct P as [P hP].
    destruct r as [t x | s], r' as [t' x' | s']. 2,3: contradiction.
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
      λ P hist,
        val w ⟨ λ r,
          match r with
          | cnv tr x => val (wf x) (shift_post tr P) (rev_append (to_trace tr) hist)
          | div s => val P (div s)
          end
        ⟩ hist.
  Proof.
    intros r r' h hp.
    destruct P as [P hP].
    destruct r as [t x | s], r' as [t' x' | s']. 2,3: contradiction.
    - simpl in h. destruct h as [et ex]. subst.
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
    intros P Q hPQ hist h.
    eapply mw. 2: exact h.
    simpl. intros [tr x| st] hf.
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
    λ P hist, ∃ (h : p), val P (cnv [] h).

  #[export] Instance reqᵂ_ismono : ∀ p, Monotonous (reqᵂ' p).
  Proof.
    intros p. intros P Q hPQ hist h.
    destruct h as [hp h].
    exists hp. apply hPQ. assumption.
  Qed.

  Definition reqᵂ (p : Prop) : W p :=
    as_wp (reqᵂ' p).

  Definition tauᵂ' : W' unit :=
    λ P hist, val P (cnv [ None ] tt).

  #[export] Instance tauᵂ_ismono : Monotonous tauᵂ'.
  Proof.
    intros P Q hPQ hist h.
    apply hPQ. assumption.
  Qed.

  Definition tauᵂ : W unit :=
    as_wp tauᵂ'.

  Definition openᵂ' (fp : path) : W' file_descr :=
    λ P hist, ∀ fd, val P (cnv [ Some (EOpen fp fd) ] fd).

  Instance openᵂ_ismono : ∀ fp, Monotonous (openᵂ' fp).
  Proof.
    intros fp. intros P Q hPQ hist h.
    intro fd.
    apply hPQ. apply h.
  Qed.

  Definition openᵂ (fp : path) : W file_descr :=
    as_wp (openᵂ' fp).

  Definition readᵂ' (fd : file_descr) : W' file_content :=
    λ P hist, is_open fd hist ∧ ∀ fc, val P (cnv [ Some (ERead fd fc) ] fc).

  Instance readᵂ_ismono : ∀ fd, Monotonous (readᵂ' fd).
  Proof.
    intros fd. intros P Q hPQ hist h.
    destruct h as [ho h].
    split.
    - assumption.
    - intro fc. apply hPQ. apply h.
  Qed.

  Definition readᵂ (fd : file_descr) : W file_content :=
    as_wp (readᵂ' fd).

  Definition closeᵂ' (fd : file_descr) : W' unit :=
    λ P hist, is_open fd hist ∧ val P (cnv [ Some (EClose fd) ] tt).

  Instance closeᵂ_ismono : ∀ fd, Monotonous (closeᵂ' fd).
  Proof.
    intros fd. intros P Q hPQ hist h.
    destruct h as [ho h].
    split.
    - assumption.
    - apply hPQ. assumption.
  Qed.

  Definition closeᵂ (fd : file_descr) : W unit :=
    as_wp (closeᵂ' fd).

  #[export] Instance Monad_W : Monad W := {|
    ret := retᵂ ;
    bind := bindᵂ
  |}.

  #[export] Instance ReqMonad_W : ReqMonad W := {|
    req := reqᵂ
  |}.

  Definition wle [A] (w₀ w₁ : W A) : Prop :=
    ∀ P hist, val w₁ P hist → val w₀ P hist.

  #[export] Instance Order_W : Order W.
  Proof.
    exists wle.
    intros A x y z h₁ h₂. intros P hist h.
    apply h₁. apply h₂.
    assumption.
  Defined.

  #[export] Instance Reflexive_wle [A] : Reflexive (wle (A := A)).
  Proof.
    intro w. intros p hist h. assumption.
  Qed.

  #[export] Instance MonoSpec_W : MonoSpec W.
  Proof.
    constructor.
    intros A B w w' wf wf' hw hwf.
    intros P hist h.
    hnf. hnf in h.
    apply hw. destruct w' as [w' mw']. eapply mw'. 2: exact h.
    simpl. intros [tr x| st] hf.
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
    λ post hist,
      ∃ (P : J → W A),
        (∀ j, iter_expand w j P ≤ᵂ P j) ∧
        val (P i) post hist.

  #[export] Instance iterᵂ_ismono [J A] (w : J → W (J + A)) (i : J) :
    Monotonous (iterᵂ' w i).
  Proof.
    intros P Q hPQ hist h.
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
    intros J A w i. intros post hist h.
    destruct h as [iᵂ [helim hi]].
    eapply helim in hi as h. simpl in h. red in h.
    simpl. red. eapply ismono. 2: exact h.
    simpl. intros [tr [j | x] | st] hh.
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
    intros post hist h'.
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
    exists (λ P hist, val w (λ x, val P (cnv [] x))).
    intros P Q hPQ hist h.
    destruct w as [w mw].
    eapply mw. 2: exact h.
    simpl. intros x. apply hPQ.
  Defined.

  #[export] Instance hlift : PureSpec W Order_W liftᵂ.
  Proof.
    constructor.
    intros A w f.
    intros P hist h.
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
    | act_reqᴹ p k => bind (reqᵂ p) (λ x, θ (k x))
    | act_iterᴹ J B g i k => bind (iterᵂ (λ i, θ (g i)) i) (λ x, θ (k x))
    | act_openᴹ fp k => bind (openᵂ fp) (λ x, θ (k x))
    | act_readᴹ fd k => bind (readᵂ fd) (λ x, θ (k x))
    | act_closeᴹ fd k => bind (closeᵂ fd) (λ x, θ k)
    end.

  Lemma bindᵂ_assoc :
    ∀ A B C (w : W A) (wf : A → W B) (wg : B → W C),
      bind w (λ x, bind (wf x) wg) ≤ᵂ bind (bind w wf) wg.
  Proof.
    intros A B C w wf wg.
    intros P hist h.
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
      as [ A x | A p k ih | A J C g ihg i k ih | A fp k ih | A fd k ih | A fd k ih]
      in B, f |- *.
      2-6: cbn - [structures.wle bind].
      2-6: etransitivity ; [| eapply bindᵂ_assoc].
      2-6: cbn - [structures.wle].
      2-6: change bindᵂ with bind.
      2-6: eapply bind_mono ; [reflexivity |].
      2-6: intro.
      2-6: apply ih.
      intros P hist h.
      simpl. simpl in h.
      eapply ismono. 2: exact h.
      apply shift_post_nil.
  Qed.

  Instance θ_reqlax : ReqLaxMorphism _ θ.
  Proof.
    constructor.
    intros p. intros post hist h.
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
    intros P hist h.
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

  Definition openᴰ fp : D file_descr (openᵂ fp).
  Proof.
    exists (openᴹ fp).
    intros P hist h. apply h.
  Defined.

  Definition readᴰ fd : D file_content (readᵂ fd).
  Proof.
    exists (readᴹ fd).
    intros P hist h. apply h.
  Defined.

  Definition closeᴰ fd : D unit (closeᵂ fd).
  Proof.
    exists (closeᴹ fd).
    intros P hist h. apply h.
  Defined.

  (** pre and post combinator

    Note: we do not need the resp_eutt for post, the generated pre will
    already take care of it.

  *)

  Definition prepostᵂ' [A] (pre : preᵂ) (post : history → run A → Prop) : W' A :=
    λ P hist, pre hist ∧ (∀ r, post hist r → val P r).

  #[export] Instance prepostᵂ_ismono [A] pre post :
    Monotonous (@prepostᵂ' A pre post).
  Proof.
    intros P Q hPQ hist h.
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
      (∀ hist, p' hist → p hist) →
      (∀ hist r, q hist r → q' hist r) →
      prepostᵂ p q ≤ᵂ prepostᵂ p' q'.
  Proof.
    intros A p p' q q' hp hq.
    intros post hist h.
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
      | cnv tr (inl j) => pre j (rev_append (to_trace tr) hist) ∧ inv (to_trace tr)
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
    clear. intros j. intros post hist h.
    simpl. red.
    simpl in h. red in h.
    destruct h as [hpre hpost].
    split. 1: assumption.
    intros [t [i | x] | s]. 2,3: contradiction.
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

  (* Alternate definition of iterᵂ using Coq coinduction. *)

  Lemma iter_expand_mono_k :
    ∀ J A (w : J → W (J + A)) (i : J) (k k' : J → W A),
      (∀ j, k j ≤ᵂ k' j) →
      iter_expand w i k ≤ᵂ iter_expand w i k'.
  Proof.
    intros J A w i k k' hk.
    unfold iter_expand. eapply bind_mono.
    - reflexivity.
    - intros [j | y].
      + eapply bind_mono. 1: reflexivity.
        intros _. apply hk.
      + reflexivity.
  Qed.

  (** Alternative semantics where we use coinductive data first.
      Essentially a particular case of interaction tree.
  *)

  Definition run_prepend [A] (tr : otrace) (r : run A) : run A :=
    match r with
    | cnv tr' x => cnv (tr ++ tr') x
    | div st => div (stream_prepend tr st)
    end.

  CoInductive itree A :=
  | iret (x : A)
  | ireq (p : Prop) (k : p → itree A)
  | iopen (p : path) (k : file_descr → itree A)
  | iread (f : file_descr) (k : file_content → itree A)
  | iclose (f : file_descr) (k : itree A)
  | itau (k : itree A).

  Arguments iret [_].
  Arguments ireq [_].
  Arguments iopen [_].
  Arguments iread [_].
  Arguments iclose [_].
  Arguments itau [_].

  (** We follow the itree practice of defining subst before bind to be able to
      use bind in other cofixpoints.
  *)

  Definition isubst [A B] (f : A → itree B) : itree A → itree B :=
    cofix _isubst (c : itree A) : itree B :=
      match c with
      | iret x => f x
      | ireq p k => ireq p (λ h, _isubst (k h))
      | iopen fp k => iopen fp (λ x, _isubst (k x))
      | iread fd k => iread fd (λ x, _isubst (k x))
      | iclose fd k => iclose fd (_isubst k)
      | itau k => itau (_isubst k)
      end.

  Definition ibind [A B] (c : itree A) (f : A → itree B) : itree B :=
    isubst f c.

  #[export] Instance Monad_itree : Monad itree := {|
    ret := iret ;
    bind := ibind
  |}.

  #[export] Instance ReqMonad_itree : ReqMonad itree := {|
    req p := ireq p (λ h, iret h)
  |}.

  CoFixpoint iiter [J A] (f : J → itree (J + A)) (i : J) : itree A :=
    bind (f i) (λ x,
      match x with
      | inl j => itau (iiter f j)
      | inr y => iret y
      end
    ).

  (* We cannot define it as a cofixpoint so we use a relation. *)
  CoInductive iwp [A] : itree A → W A → Prop :=
  | wp_ret : ∀ x, iwp (iret x) (retᵂ x)
  | wp_req :
      ∀ p k wk,
        (∀ h, iwp (k h) (wk h)) →
        iwp (ireq p k) (bind (reqᵂ p) wk)
  | wp_open :
      ∀ fp k wk,
        (∀ fd, iwp (k fd) (wk fd)) →
        iwp (iopen fp k) (bind (openᵂ fp) wk)
  | wp_read :
      ∀ fd k wk,
        (∀ fc, iwp (k fc) (wk fc)) →
        iwp (iread fd k) (bind (readᵂ fd) wk)
  | wp_close :
      ∀ fd k wk,
        iwp k wk →
        iwp (iclose fd k) (bind (closeᵂ fd) (λ _, wk))
  | wp_tau :
      ∀ k wk,
        iwp k wk →
        iwp (itau k) (bind tauᵂ (λ _, wk)).

  (* Alternative, but that means problems with W' vs W *)
  (* CoInductive iwp [A] : itree A → W' A :=
  | wp_ret :
      ∀ x (post : postᵂ A) hist,
        val post (cnv [] x) →
        iwp (iret x) post hist. *)

  Definition θ_itree [A] (t : itree A) : W' A :=
    λ post hist,
      ∀ w, iwp t w → val w post hist.

  (* Interpretation from M *)

  Fixpoint to_itree [A] (c : M A) : itree A :=
    match c with
    | retᴹ x => iret x
    | act_reqᴹ p k => ireq p (λ h, to_itree (k h))
    | act_iterᴹ J B g i k => bind (iiter (λ j, to_itree (g j)) i) (λ x, to_itree (k x))
    | act_openᴹ fp k => iopen fp (λ x, to_itree (k x))
    | act_readᴹ fd k => iread fd (λ x, to_itree (k x))
    | act_closeᴹ fd k => iclose fd (to_itree k)
    end.

  Definition θalt [A] (c : M A) : W' A :=
    θ_itree (to_itree c).

  (* Equivalence *)

  Set Equations With UIP.

  Axiom uipa : ∀ A, UIP A.
  #[local] Existing Instance uipa.

  Definition weq [A] (w w' : W A) :=
    ∀ post hist, val w post hist ↔ val w' post hist.

  Notation "x =ᵂ y" := (weq x y) (at level 80).

  Lemma weq_eq :
    ∀ A (w w' : W A),
      w =ᵂ w' →
      w = w'.
  Proof.
    intros A w w' e.
    apply sig_ext. extensionality post. extensionality hist.
    apply propositional_extensionality. apply e.
  Qed.

  Lemma bind_ret :
    ∀ A B x (wf : A → W B),
      bindᵂ (retᵂ x) wf = wf x.
  Proof.
    intros A B x wf.
    apply weq_eq. intros post hist. split. all: intro h.
    - simpl in h. eapply ismono. 2: exact h.
      simpl. intros [] hh. all: auto.
    - simpl. eapply ismono. 2: exact h.
      simpl. intros [] hh. all: auto.
  Qed.

  Lemma bind_assoc :
    ∀ A B C (w : W A) (wf : A → W B) (wg : B → W C),
      bindᵂ w (λ x, bindᵂ (wf x) wg) = bindᵂ (bindᵂ w wf) wg.
  Proof.
    intros A B C w wf wg.
    apply weq_eq. intros post hist. split.
    - simpl. intro h. red. red in h.
      eapply ismono. 2: exact h.
      simpl. intros []. 2: auto.
      intro hh. red in hh.
      eapply ismono. 2: exact hh.
      simpl. intros []. 2: auto.
      intro h3.
      rewrite to_trace_app. rewrite rev_append_rev. rewrite rev_app_distr.
      rewrite <- app_assoc.
      rewrite 2!rev_append_rev in h3.
      eapply ismono. 2: exact h3.
      simpl. intros [] h4.
      + rewrite <- app_assoc. assumption.
      + rewrite <- stream_prepend_app. assumption.
    - eapply bindᵂ_assoc.
  Qed.

  Definition itree_unfold [A] (t : itree A) : itree A :=
    match t with
    | iret x => iret x
    | ireq p k => ireq p k
    | iopen fp k => iopen fp k
    | iread fd k => iread fd k
    | iclose fd k => iclose fd k
    | itau k => itau k
    end.

  Lemma itree_unfold_eq :
    ∀ A (t : itree A), t = itree_unfold t.
  Proof.
    intros A t.
    destruct t. all: reflexivity.
  Qed.

  Ltac cofold f :=
    lazymatch goal with
    | |- context C[ cofix foo : _ := _ ] =>
      let C' := context C[f] in
      change C'
    end.

  Lemma iwp_bind :
    ∀ A B (t : itree A) (f : A → itree B) w wf,
      iwp t w →
      (∀ x, iwp (f x) (wf x)) →
      iwp (ibind t f) (bindᵂ w wf).
  Proof.
    intros A B t f w wf h hf.
    unfold ibind.
    revert t w h. cofix cih. intros t w h.
    destruct t.
    - inversion h. rewrite bind_ret.
      rewrite (itree_unfold_eq _ (isubst _ _)).
      unfold isubst. unfold itree_unfold.
      fold (itree_unfold (f x)).
      rewrite <- (itree_unfold_eq _ (f x)).
      apply hf.
    - inversion h.
      rewrite (itree_unfold_eq _ (isubst _ _)).
      unfold isubst. unfold itree_unfold. cofold (isubst f).
      rewrite <- bind_assoc.
      constructor.
      intro prf. eapply cih. noconf H1. apply H2.
    - inversion h.
      rewrite (itree_unfold_eq _ (isubst _ _)).
      unfold isubst. unfold itree_unfold. cofold (isubst f).
      rewrite <- bind_assoc.
      constructor.
      intro fd. eapply cih. noconf H1. apply H2.
    - inversion h.
      rewrite (itree_unfold_eq _ (isubst _ _)).
      unfold isubst. unfold itree_unfold. cofold (isubst f).
      rewrite <- bind_assoc.
      constructor.
      intro fc. eapply cih. noconf H1. apply H2.
    - inversion h.
      rewrite (itree_unfold_eq _ (isubst _ _)).
      unfold isubst. unfold itree_unfold. cofold (isubst f).
      rewrite <- bind_assoc.
      constructor.
      eapply cih. assumption.
    - inversion h.
      rewrite (itree_unfold_eq _ (isubst _ _)).
      unfold isubst. unfold itree_unfold. cofold (isubst f).
      rewrite <- bind_assoc.
      constructor.
      eapply cih. assumption.
  Qed.

  Lemma iterᵂ_unfold_eq :
    ∀ J A (w : J → W (J + A)) (i : J),
    iterᵂ w i = iter_expand w i (iterᵂ w).
  Proof.
    intros J A w i.
    apply weq_eq. split.
    - apply iterᵂ_unfold.
    - apply iterᵂ_fold.
  Qed.

  Lemma iwp_to_itree_θ :
    ∀ A (c : M A),
      iwp (to_itree c) (θ c).
  Proof.
    intros A c.
    induction c as [ A x | A p k ih | A J C g ihg i k ih | A fp k ih | A fd k ih | A fd k ih].
    - constructor.
    - simpl. constructor. assumption.
    - simpl. apply iwp_bind. 2: eapply ih.
      revert i. cofix f. intro i.
      rewrite (itree_unfold_eq _ (iiter _ _)).
      unfold iiter. unfold itree_unfold. cofold iiter.
      lazymatch goal with
      | |- iwp ?t ?w =>
        lazymatch t with
        | context [Monad_itree.(bind) ?c ?f] =>
          change (iwp (itree_unfold (Monad_itree.(bind) c f)) w) ;
          rewrite <- (itree_unfold_eq _ (Monad_itree.(bind) c f))
          (* fold (itree_unfold (Monad_itree.(bind) c f)) *)
        end
      end.
      rewrite iterᵂ_unfold_eq.
      apply iwp_bind.
      + apply ihg.
      + intros [j | x].
        * constructor. apply f. Fail Guarded. (* because of iwp_bind *)
        * constructor.
    - simpl. constructor. assumption.
    - simpl. constructor. assumption.
    - simpl. constructor. assumption.
  Admitted.

  Lemma equiv_θ :
    ∀ A (c : M A) post hist,
      val (θ c) post hist ↔ θalt c post hist.
  Proof.
    intros A c post hist. split.
    - induction c as [ A x | A p k ih | A J C g ihg i k ih | A fp k ih | A fd k ih | A fd k ih] in post, hist |- *.
      all: intros h w hw.
      + inversion hw. subst. assumption.
      + inversion hw. subst.
        noconf H1. simpl. simpl in h. eapply ismono. 2: eapply h.
        simpl. intros [tr prf |] hh. 2: auto.
        eapply ih in hh. apply hh. eauto.
      + admit.
      + inversion hw. subst.
        simpl. simpl in h. eapply ismono. 2: apply h.
        simpl. intros [tr x |] hh. 2: auto.
        eapply ih in hh. apply hh. eauto.
      + inversion hw. subst.
        simpl. simpl in h. eapply ismono. 2: apply h.
        simpl. intros [tr x |] hh. 2: auto.
        eapply ih in hh. apply hh. eauto.
      + inversion hw. subst.
        simpl. simpl in h. eapply ismono. 2: apply h.
        simpl. intros [tr x |] hh. 2: auto.
        eapply ih in hh. apply hh. eauto.
    - intros h. apply h. apply iwp_to_itree_θ.
  Admitted.

End IODiv.
