(* Non-termination *)

From Coq Require Import Utf8 RelationClasses List.
From PDM Require Import util structures guarded PURE GuardedPDM.

Import ListNotations.

Set Default Goal Selector "!".
Set Printing Projections.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive M A :=
| retᴹ (x : A)
| act_reqᴹ (p : Prop) (k : p → M A)
(* | act_iterᴹ {I B : Type} (f : I → M (I + B)%type) (i : I) (k : B → M A). *)
| act_fixᴹ (D C : Type) (F : (D → C) → (D → M C)) (i : D) (k : C → M A).

Arguments retᴹ [_].
Arguments act_reqᴹ [_].
Arguments act_fixᴹ [_].

Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
  match c with
  | retᴹ x => f x
  | act_reqᴹ p k => act_reqᴹ p (λ h, bindᴹ (k h) f)
  | act_fixᴹ D C F i k => act_fixᴹ D C F i (λ z, bindᴹ (k z) f)
  end.

#[export] Instance Monad_M : Monad M := {|
  ret := retᴹ ;
  bind := bindᴹ
|}.

#[export] Instance ReqMonad_M : ReqMonad M := {|
  req p := act_reqᴹ p (λ h, retᴹ h)
|}.

Definition fixᴹ [D C] F i :=
  act_fixᴹ D C F i (λ x, retᴹ x).

Reserved Notation "u ▹ v" (at level 80).

Inductive red {A} : M A → M A → Prop :=

| prove_req :
    ∀ p k h,
      act_reqᴹ p k ▹ k h

(* Not clear how to unfold fix properly *)
(* | unfold_fix :
    ∀ D C F i k,
      act_fixᴹ D C F i k ▹ ? *)

where "u ▹ v" := (red u v).