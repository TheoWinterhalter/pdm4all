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
    λ P hist s₀, ∃ fd, P (cnv [ EOpen fp fd ] s₀ fd).

  Instance openᵂ_ismono : ∀ fp, Monotonous (openᵂ' fp).
  Proof.
    intros fp. intros P Q hPQ hist s₀ h.
    destruct h as [fd h].
    exists fd. apply hPQ. assumption.
  Qed.

  Definition openᵂ (fp : path) : W file_descr :=
    as_wp (openᵂ' fp).

  Definition readᵂ' (fd : file_descr) : W' file_content :=
    λ P hist s₀, is_open fd hist ∧ ∃ fc, P (cnv [ ERead fd fc ] s₀ fc).

  Instance readᵂ_ismono : ∀ fd, Monotonous (readᵂ' fd).
  Proof.
    intros fd. intros P Q hPQ hist s₀ h.
    destruct h as [ho [fc h]].
    split.
    - assumption.
    - exists fc. apply hPQ. assumption.
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

  (* Iterate (n+1) times w (by binding it) *)
  Fixpoint niterᵂ [J A] (n : nat) (w : J → W (J + A)) (i : J) : W (J + A) :=
    match n with
    | 0 => w i
    | S n =>
      bindᵂ (w i) (λ x,
        match x with
        | inl j => niterᵂ n w j
        | inr y => retᵂ (inr y)
        end
      )
    end.

  Definition iterᵂ' [J A] (w : J → W (J + A)) (i : J) : W' A :=
    λ P hist s₀,
      (* Finite iteration *)
      (∀ n tr s₁ x,
        val (niterᵂ n w i) (λ r, r = cnv tr s₁ (inr x)) hist s₀ →
        P (cnv tr s₁ x)
      ) ∧
      (* Finite iteration with final branch diverging *)
      (∀ n st,
        val (niterᵂ n w i) (λ r, r = div st) hist s₀ →
        P (div st)
      ) ∧
      (* Infinite iteration *)
      (∀ (js : nat → J) (trs : nat → trace) (ss : nat → state) s,
        val (w i) (λ r, r = cnv (trs 0) (ss 0) (inl (js 0))) hist s₀ →
        (∀ n,
          val (w (js n))
            (λ r, r = cnv (trs (S n)) (ss (S n)) (inl (js (S n))))
            (rev_append (ttrunc trs n) hist)
            (ss n)
        ) →
        s ⊑ trs →
        P (div s)
      ).

  #[export] Instance iterᵂ_ismono [J A] (w : J → W (J + A)) (i : J) :
    Monotonous (iterᵂ' w i).
  Proof.
    intros P Q hPQ hist s₀ h.
    destruct h as [hfi [hdb hdi]].
    split. 2: split.
    - intros n tr s₁ x h.
      apply hPQ. eapply hfi. eassumption.
    - intros n st h.
      apply hPQ. eapply hdb. eassumption.
    - intros js trs ss s hi hn hs.
      apply hPQ. eapply hdi. all: eassumption.
  Qed.

  Definition iterᵂ [J A] w i :=
    as_wp (@iterᵂ' A J w i).

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

End IIOStDiv.