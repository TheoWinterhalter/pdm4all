(* Construction of a PDM for a free monad *)

From Coq Require Import Utf8 RelationClasses.
From PDM Require Import util structures guarded PURE PDM.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Section Free.

  Context (action : Type).
  Context (dom : action → Type) (cod : ∀ a (x : dom a), Type).

  Inductive M (A : Type) :=
  | retᴹ (x : A)
  | actᴹ (a : action) (v : dom a) (k : cod a v → M A)
  | reqᴹ (p : Prop) (k : p → M A).

  Arguments retᴹ [_].
  Arguments actᴹ [_].
  Arguments reqᴹ [_].

  Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
    match c with
    | retᴹ x => f x
    | actᴹ a v k => actᴹ a v (λ x, bindᴹ (k x) f)
    | reqᴹ p k => reqᴹ p (λ x, bindᴹ (k x) f)
    end.

  Instance Monad_M : Monad M := {|
    ret := retᴹ ;
    bind := bindᴹ
  |}.

  Instance ReqMonad_M : ReqMonad M := {|
    req p := reqᴹ p (λ h, retᴹ h)
  |}.

  (* For the specification monad, we take any one that has assertions.
    Given that it is easy to construct for those we are interested in in
    practice this is feature. The user will want to choose the shape of the
    specification monad.

    That said, this ends up being a lot of requirements on W, it would be good
    to package them and maybe see if we should always define reqᵂ in terms of
    liftᵂ.
  *)

  Context {W} `{ReqMonad W} {Word : Order W} (hmono : MonoSpec W).
  Context {Wlaws : MonadLaws W}.
  Context (actionᵂ : ∀ (a : action) (v : dom a), W (cod a v)).

  Fixpoint θ [A] (c : M A) : W A :=
    match c with
    | retᴹ x => ret x
    | actᴹ a v k => bind (actionᵂ a v) (λ x, θ (k x))
    | reqᴹ p k => bind (req p) (λ x, θ (k x))
    end.

  Context {hr : ∀ A, Reflexive (wle (A := A))}.

  Instance θ_lax : LaxMorphism θ.
  Proof.
    constructor.
    - intros A x.
      cbn. reflexivity.
    - intros A B c f.
      induction c as [| ??? ih | ?? ih] in B, f |- *.
      + cbn. rewrite structures.left_id. reflexivity.
      + cbn. rewrite structures.assoc.
        apply bind_mono. 1: reflexivity.
        intro x. apply ih.
      + cbn. rewrite structures.assoc.
        apply bind_mono. 1: reflexivity.
        intro x. apply ih.
  Qed.

  Instance θ_reqlax : ReqLaxMorphism _ θ.
  Proof.
    constructor.
    intros p. cbn.
    rewrite structures.right_id. reflexivity.
  Qed.

  Definition D A w : Type :=
    PDM.D (θ := θ) A w.

  Instance DijkstraMonad_D : DijkstraMonad D :=
    PDM.DijkstraMonad_D hmono θ_lax.

  (* Lift from PURE *)

  Context (liftᵂ : spec_lift_pure W).
  Context (hlift : PureSpec W Word liftᵂ).

  Definition liftᴾ :=
    liftᴾ (M := M) (W := W) hmono θ_lax θ_reqlax hlift.

  (* TODO missing actions *)

End Free.