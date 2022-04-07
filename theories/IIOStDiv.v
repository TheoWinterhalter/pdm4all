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

  (* TODO MOVE *)
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

  Lemma strace_prepend_nil :
    ∀ s,
      strace_prepend [] s = s.
  Proof.
    intros [].
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma shift_post_nil :
    ∀ A (P : postᵂ A) r,
      shift_post [] P r → P r.
  Proof.
    intros A P r h.
    destruct r.
    - apply h.
    - simpl in h. rewrite strace_prepend_nil in h. assumption.
  Qed.

  Lemma shift_post_nil_imp :
    ∀ A (P : postᵂ A) r,
      P r → shift_post [] P r.
  Proof.
    intros A P r h.
    destruct r.
    - apply h.
    - simpl. rewrite strace_prepend_nil. assumption.
  Qed.

  Lemma shift_post_mono :
    ∀ A tr (P Q : postᵂ A),
      (∀ r, P r → Q r) →
      ∀ r, shift_post tr P r → shift_post tr Q r.
  Proof.
    intros A tr P Q h r hP.
    destruct r.
    - apply h. assumption.
    - apply h. assumption.
  Qed.

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

  Lemma strace_prepend_app :
    ∀ t t' s,
      strace_prepend t (strace_prepend t' s) = strace_prepend (t ++ t') s.
  Proof.
    intros t t' [].
    - simpl. rewrite app_assoc. reflexivity.
    - simpl. rewrite stream_prepend_app. reflexivity.
  Qed.

  Lemma shift_post_app :
    ∀ A t t' (P : postᵂ A) r,
      shift_post (t' ++ t) P r → shift_post t (shift_post t' P) r.
  Proof.
    intros A t t' P [] h.
    - simpl in *. rewrite app_assoc. assumption.
    - simpl in *. rewrite strace_prepend_app. assumption.
  Qed.

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

  #[export] Instance pure_wp_refl [A] : Reflexive (wle (A := A)).
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

  Instance θ_lax : LaxMorphism θ.
  Proof.
    constructor.
    - intros A x.
      reflexivity.
    - intros A B c f.
      induction c
      as [ A x | A p k ih | A J C g ihg i k ih | A k ih | A p k ih | A fp k ih | A fd k ih | A fd k ih | A k ih]
      in B, f |- *.
      all: intros P hist s₀ h.
      + simpl. simpl in h. red in h. simpl in h.
        eapply ismono. 2: exact h.
        apply shift_post_nil.
      + destruct h as [hp h]. exists hp.
        apply ih. simpl. simpl in h. red.
        eapply ismono. 2: exact h.
        intros r hr. apply shift_post_nil in hr.
        destruct r.
        * eapply ismono. 2: exact hr.
          apply shift_post_mono.
          apply shift_post_nil_imp.
        * apply shift_post_nil_imp. assumption.
      + destruct h as [h1 [h2 h3]].
        split. 2: split.
        * intros n tr s₁ x h.
          apply ih. simpl. red. eapply ismono.
          2:{ eapply h1. eassumption. }
          intros []. all: simpl. 2: auto.
          rewrite !rev_append_rev. rewrite rev_app_distr. rewrite app_assoc.
          intro. eapply ismono. 2: eassumption.
          apply shift_post_app.
        * intros n st h.
          eapply h2. eassumption.
        * intros js trs ss s hi hn hs.
          eapply h3. all: eassumption.
      + simpl. red. simpl.
        simpl in h. red in h. simpl in h.
        apply ih. simpl. red.
        eapply ismono. 2: exact h.
        intros [].
        * simpl. intro. eapply ismono. 2: eassumption.
          apply shift_post_mono. apply shift_post_nil_imp.
        * simpl. auto.
      + simpl. red. simpl.
        simpl in h. red in h. simpl in h.
        apply ih. simpl. red.
        eapply ismono. 2: exact h.
        intros [].
        * simpl. intro. eapply ismono. 2: eassumption.
          apply shift_post_mono. apply shift_post_nil_imp.
        * simpl. auto.
      + simpl. red. simpl.
        simpl in h. red in h. simpl in h.
        intro fd.
        apply ih. simpl. red.
        eapply ismono. 2: apply h.
        intros [].
        * simpl. intro. eapply ismono. 2: eassumption.
          intros. apply shift_post_app. assumption.
        * simpl. auto.
      + simpl. red. simpl.
        simpl in h. red in h. simpl in h.
        destruct h as [ho h].
        split. 1: assumption.
        intro fc.
        apply ih. simpl. red.
        eapply ismono. 2: apply h.
        intros [].
        * simpl. intro. eapply ismono. 2: eassumption.
          intros. apply shift_post_app. assumption.
        * simpl. auto.
      + simpl. red. simpl.
        simpl in h. red in h. simpl in h.
        destruct h as [ho h]. split. 1: apply ho.
        apply ih. simpl. red.
        eapply ismono. 2: exact h.
        intros [].
        * simpl. intro. eapply ismono. 2: eassumption.
          intros. apply shift_post_app. assumption.
        * simpl. auto.
      + simpl. red. simpl.
        simpl in h. red in h. simpl in h.
        apply ih. simpl. red.
        eapply ismono. 2: exact h.
        intros [].
        * simpl. intro. eapply ismono. 2: eassumption.
          apply shift_post_mono. apply shift_post_nil_imp.
        * simpl. auto.
  Qed.

  Instance θ_reqlax : ReqLaxMorphism _ θ.
  Proof.
    constructor.
    intros p. intros post hist s₀ h.
    simpl. red. simpl.
    simpl in h. red in h.
    destruct h as [hp h]. exists hp.
    red. apply shift_post_nil_imp. assumption.
  Qed.

  Definition D A w : Type :=
    PDM.D (θ := θ) A w.

  Instance DijkstraMonad_D : DijkstraMonad D :=
    PDM.DijkstraMonad_D WMono θ_lax.

  (* Lift from PURE *)

  Definition liftᴾ : ∀ A w, PURE A w → D A (liftᵂ w) :=
    PDM.liftᴾ (M := M) (W := W) WMono θ_lax θ_reqlax hlift.

  (* Actions *)

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

  Definition invᵂ A :=
    (* trace → state → Prop. *)
    postᵂ A.

  Definition iter_inv_bodyᵂ [J A] (pre : J → preᵂ) (inv : invᵂ (J + A)) (i : J) : W (J + A) :=
    prepostᵂ (pre i) (λ hist r,
      inv r ∧
      match r with
      | cnv tr s (inl j) => pre j (rev_append tr hist) s
      | cnv tr s (inr x) => True
      | div st => True
      end
    ).

  Definition iter_invᵂ [J A] (pre : J → preᵂ) (inv : invᵂ (J + A)) (i : J) : W A :=
    prepostᵂ (pre i) (λ hist r,
      match r with
      | cnv tr s x => inv (cnv tr s (inr x))
      | div st => inv (div st)
      end
    ).

  Definition iter_invᴰ [J A] pre inv (f : ∀ (j : J), D (J + A) (iter_inv_bodyᵂ pre inv j)) (i : J) :
    D A (iter_invᵂ pre inv i).
  Proof.
    exists (iterᴹ (λ j, val (f j)) i).
    intros P hist s₀ [hpre hpost].
    split. 2: split.
    - intros n tr s₁ x h.
      simpl. red. red. rewrite app_nil_r.
      eapply hpost.
      induction n.
      + simpl in h. (* Variance problem... *) give_up.
      + give_up.
    - give_up.
    - give_up.
  Abort.

End IIOStDiv.