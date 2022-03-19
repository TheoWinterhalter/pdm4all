(*** Non-termination with instrumented I/O and state

  The partial Dijstra Monad comes with a computation monad that is essentially
  a syntax monad (using a free monad) and the specification gives meaning to
  the different operations, including the iteration operator.

  For I/O we assume we can open and close files as well as read them.
  Because I/O is instrumented we can also read the history up to now.

*)

From Coq Require Import Utf8 RelationClasses List PropExtensionality
  FunctionalExtensionality.
From PDM Require Import util structures guarded PURE.
From PDM Require PDM.

Import ListNotations.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

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

  (* A strace refining a stream of traces *)
  Definition trace_refine (t : strace) (s : nat → trace) : Prop :=
    match t with
    | fintrace t => ∃ n, ∀ m, n ≤ m → t = ttrunc s m
    | inftrace t => ∀ n, ttrunc s n = strunc t (length (ttrunc s n))
    end.

  Notation "t ⊑ s" := (trace_refine t s) (at level 80).

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

  Definition iterᴹ [J A] (f : J → M (J + A)) (i : J) :=
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

  (** Specifiation monad *)

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

  Definition retᵂ' [A] (x : A) : W' A :=
    λ P hist s₀, P (cnv [] s₀ x).

  #[export] Instance retᵂ_ismono [A] (x : A) : Monotonous (retᵂ' x).
  Proof.
    intros P Q hPQ hist s₀ h.
    apply hPQ. apply h.
  Qed.

  Definition retᵂ [A] (x : A) : W A :=
    as_wp (retᵂ' x).

  Definition bindᵂ' [A B] (w : W A) (wf : A → W B) : W' B :=
    λ P hist s₀,
      val w (λ r,
        match r with
        | cnv tr s₁ x => val (wf x) P (rev_append tr hist) s₁
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
      assumption.
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

  #[export] Instance Monad_W : Monad W := {|
    ret := retᵂ ;
    bind := bindᵂ
  |}.

  #[export] Instance ReqMonad_W : ReqMonad W := {|
    req := reqᵂ
  |}.

  (* TODO spec of actions *)

End IIOStDiv.