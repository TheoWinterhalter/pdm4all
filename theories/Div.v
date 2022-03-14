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
| act_iterᴹ (J B : Type) (f : J → M (J + B)%type) (i : J) (k : B → M A).
(* | act_fixᴹ (D C : Type) (F : (D → C) → (D → M C)) (i : D) (k : C → M A). *)
(* | act_fixᴹ (C : Type) (F : C → M C) (k : C → M A). *)

Arguments retᴹ [_].
Arguments act_reqᴹ [_].
(* Arguments act_fixᴹ [_]. *)
Arguments act_iterᴹ [_].

Fixpoint bindᴹ [A B] (c : M A) (f : A → M B) : M B :=
  match c with
  | retᴹ x => f x
  | act_reqᴹ p k => act_reqᴹ p (λ h, bindᴹ (k h) f)
  | act_iterᴹ J B g i k => act_iterᴹ J B g i (λ h, bindᴹ (k h) f)
  (* | act_fixᴹ D C F i k => act_fixᴹ D C F i (λ z, bindᴹ (k z) f) *)
  (* | act_fixᴹ C F k => act_fixᴹ C F (λ z, bindᴹ (k z) f) *)
  end.

#[export] Instance Monad_M : Monad M := {|
  ret := retᴹ ;
  bind := bindᴹ
|}.

#[export] Instance ReqMonad_M : ReqMonad M := {|
  req p := act_reqᴹ p (λ h, retᴹ h)
|}.

(* Definition fixᴹ [D C] F i :=
  act_fixᴹ D C F i (λ x, retᴹ x). *)

(* Definition fixᴹ [C] F :=
  act_fixᴹ C F (λ x, retᴹ x). *)

Definition iterᴹ [J A] (f : J → M (J + A)) (i : J) :=
  act_iterᴹ J A f i (λ x, ret x).

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

(* Not clear how to unfold fix properly *)
(* | unfold_fix :
    ∀ D C F i k,
      act_fixᴹ D C F i k ▹ ? *)

(* Not great operationally is it? We need a rule to make fix disappear *)
(* Not going to get one with this determistic thing. *)
(* | unfold_fix :
    ∀ C F k,
      act_fixᴹ C F k ▹ bind (fixᴹ F) (λ x, bind (F x) k) *)

| iter_step :
    ∀ J B f i k,
      act_iterᴹ J B f i k ▹ bind (iter_one f i) k

where "u ▹ v" := (red u v).