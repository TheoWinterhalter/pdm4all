(** Non-determinsim partial DM *)

module ND

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics
open FStar.Classical
open FStar.Monotonic.Pure

(** Computation monad *)

let m a = pre : pure_pre & (squash pre -> list a)

let pre_of #a (t : m a) : pure_pre =
  let (| pre , f |) = t in pre

let val_of #a (t : m a) : Pure (list a) (requires pre_of t) (ensures fun _ -> True) =
  let (| pre, f |) = t in f ()

let m_return #a (x : a) : m a =
  (| True , (fun _ -> [ x ]) |)

let rec ref_list #a (l : list a) : list (x : a { x `memP` l }) =
  match l with
  | [] -> []
  | x :: l' -> x :: List.Tot.map #_ #(y:a { y `memP` l}) (fun (y : a { y `memP` l' }) -> y) (ref_list l')

let m_bind #a #b (c : m a) (f : a -> m b) : m b =
  (| (pre_of c /\ (forall x. x `memP` val_of c ==> pre_of (f x))) ,
    (fun _ ->
      concatMap (fun (x : a { x `memP` (val_of c) }) -> val_of (f x)) (ref_list (val_of c))
    )
  |)

let m_req (p : Type0) : m (squash p) =
  (| p , (fun h -> [ h ]) |)

(** Specification monad *)

let wpre = Type0
let wpost a = a -> Type0

let wp' a = wpost a -> wpre

let wp a = w : wp' a { pure_wp_monotonic a w }

unfold
let as_wp #a (w : wp' a) :
  Pure (wp a) (requires is_monotonic w) (ensures fun r -> r == w)
= intro_pure_wp_monotonicity w ; w

unfold
let _wle #a (w1 w2 : wp a) =
  forall x. w2 x ==> w1 x

let wle #a (w1 w2 : wp a) =
  _wle w1 w2

unfold
let _w_return #a (x : a) : wp a =
  as_wp (fun post -> post x)

let w_return #a (x : a) : wp a =
  _w_return x

unfold
let _w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  elim_pure_wp_monotonicity w ;
  introduce forall x. is_monotonic (wf x)
  with begin
    elim_pure_wp_monotonicity (wf x)
  end ;
  as_wp (fun post -> w (fun x -> wf x post))

let w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  _w_bind w wf

let w_req (p : Type0) : wp (squash p) =
  as_wp (fun post -> p /\ post (Squash.get_proof p))

(** Effect observation *)

let theta #a (c : m a) : wp a =
  as_wp (fun post -> pre_of c /\ (forall x. x `memP` val_of c ==> post x))

(** Dijkstra monad *)

let dm a (w : wp a) =
  c : m a { theta c `wle` w }

let d_return #a (x : a) : dm a (w_return x) =
  m_return x

let rec memP_append_invert #a (x : a) (l l' : list a) :
  Lemma
    (requires x `memP` (l @ l'))
    (ensures x `memP` l \/ x `memP` l')
= match l with
  | [] -> ()
  | e :: tl ->
    eliminate x == e \/ x `memP` (tl @ l')
    returns x `memP` l \/ x `memP` l'
    with _. ()
    and _. memP_append_invert x tl l'

let rec memP_concatMap_inv #a #b (c : list a) (f : a -> list b) y :
  Lemma
    (requires y `memP` concatMap f c)
    (ensures exists x. x `memP` c /\ y `memP` f x)
= match c with
  | e :: l ->
    memP_append_invert y (f e) (concatMap f l) ;
    eliminate y `memP` f e \/ y `memP` concatMap f l
    returns exists x. x `memP` c /\ y `memP` f x
    with _. ()
    and _. memP_concatMap_inv l f y

let theta_bind #a #b (c : m a) (f : a -> m b) :
  Lemma (theta (m_bind c f) `wle` w_bind (theta c) (fun x -> theta (f x)))
= introduce forall post. w_bind (theta c) (fun x -> theta (f x)) post ==> theta (m_bind c f) post
  with begin
    introduce w_bind (theta c) (fun x -> theta (f x)) post ==> theta (m_bind c f) post
    with _. begin
      assert (pre_of (m_bind c f)) ;
      introduce forall x. x `memP` val_of (m_bind c f) ==> post x
      with begin
        introduce x `memP` val_of (m_bind c f) ==> post x
        with _. begin
          assert (theta c (fun x -> theta (f x) post)) ;
          assert (forall z. z `memP` val_of c ==> theta (f z) (fun x -> post x)) ;
          assert (forall z z'. z `memP` val_of c /\ z' `memP` val_of (f z) ==> post z') ;
          memP_concatMap_inv (ref_list (val_of c)) (fun x -> val_of (f x)) x
        end
      end
    end
  end

let d_bind #a #b #w (#wf : a -> wp b) (c : dm a w) (f : (x : a) -> dm b (wf x)) : dm b (w_bind w wf) =
  theta_bind c f ;
  m_bind c f

let d_req (p : Type0) : dm (squash p) (w_req p) =
  m_req p

let d_subcomp #a #w1 #w2 (c : dm a w1) :
  Pure (dm a w2) (requires w1 `wle` w2) (ensures fun _ -> True)
= c

let w_if_then_else #a (w1 w2 : wp a) (b : bool) : wp a =
  elim_pure_wp_monotonicity w1 ;
  elim_pure_wp_monotonicity w2 ;
  as_wp (fun post -> (b ==> w1 post) /\ (~ b ==> w2 post))

let if_then_else (a : Type) (w1 w2 : wp a) (f : dm a w1) (g : dm a w2) (b : bool) : Type =
  dm a (w_if_then_else w1 w2 b)

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r)
= elim_pure_wp_monotonicity_forall () ;
  f ()

unfold
let wlift #a (w : pure_wp a) : wp a =
  w

let as_requires_wlift #a (w : pure_wp a) :
  Lemma (forall post. wlift w post ==> as_requires w)
= assert (forall post (x : a). post x ==> True) ;
  elim_pure_wp_monotonicity w ;
  assert (forall post. w post ==> w (fun _ -> True)) ;
  assert (forall post. (True ==> w post) ==> w (fun _ -> True))

let lift_pure (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) : dm a (wlift w) =
  as_requires_wlift w ;
  d_bind #_ #_ #_ #(fun _ -> w_return (elim_pure #a #w f)) (d_req (as_requires w)) (fun _ ->
      let r = elim_pure #a #w f in
      let r' : dm a (w_return r) = d_return r in
      r'
  )

(** Recast return and bind so that they have effect-friendly types *)

let return a (x : a) : dm a (_w_return x) =
  d_return x

let bind a b w wf c f : dm b (_w_bind w wf) =
  d_bind #a #b #w #wf c f

let subcomp a w1 w2 (c : dm a w1) :
  Pure (dm a w2) (requires w1 `_wle` w2) (ensures fun _ -> True)
= d_subcomp c

[@@allow_informative_binders]
reflectable reifiable total layered_effect {
  NDw : a:Type -> w:wp a -> Effect
  with
    repr         = dm ;
    return       = return ;
    bind         = bind ;
    subcomp      = subcomp ;
    if_then_else = if_then_else
}

sub_effect PURE ~> NDw = lift_pure

unfold
let wprepost #a (pre : Type0) (post : a -> Pure Type0 (requires pre) (ensures fun _ -> True)) : wp a =
  as_wp (fun p -> pre /\ (forall x. post x ==> p x))

effect ND (a : Type) (pre : Type0) (post : a -> Pure Type0 (requires pre) (ensures fun _ -> True)) =
  NDw a (wprepost pre post)

(** Action *)

let m_choose #a (l : list a) : m a =
  (| True , (fun _ -> l) |)

unfold
let w_choose #a (l : list a) : wp a =
  as_wp (fun post -> forall x. x `memP` l ==> post x)

let d_choose #a (l : list a) : dm a (w_choose l) =
  m_choose l

let choose #a (l : list a) : ND a (requires True) (ensures fun r -> r `memP` l) =
  ND?.reflect (subcomp _ _ _ (d_choose l))

(** Some tests for ND *)

let test_assert p : ND unit (requires p) (ensures fun r -> True) =
  assert p

let partial_match (l : list nat) : ND unit (requires l <> []) (ensures fun r -> True) =
  match l with
  | x :: r -> ()

let partial_match_choose (l : list nat) : ND nat (requires l <> []) (ensures fun r -> r `memP` tail l) =
  match l with
  | x :: r -> choose r

assume val p : Type0
assume val p' : Type0
assume val pure_lemma (_ : unit) : Lemma p
assume val some_f (_ : squash p) : ND unit (requires True) (ensures fun _ -> True)
assume val some_f' : unit -> ND unit (requires p) (ensures fun _ -> p')

let pure_lemma_test () : ND unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f ()

let pure_lemma_test2 () : ND unit (requires True) (ensures fun _ -> True) =
  pure_lemma () ;
  some_f () ;
  some_f' () ;
  assert p'

let rec easy_rec (n : nat) : ND nat (requires True) (ensures fun _ -> True) =
  if n = 0 then 0 else easy_rec (n - 1)

let rec some_rec_tot (n : nat) : nat =
  if n > 3
  then 2 + some_rec_tot (n -3)
  else 1

[@expect_failure]
let rec some_rec (n : nat) : ND nat (requires True) (ensures fun _ -> True) =
  if n > 3
  then 2 + some_rec (n -3)
  else 1

let rec some_rec (n : nat) : ND nat (requires True) (ensures fun _ -> True) =
  if n > 3
  then begin
    let x = some_rec (n-3) in
    2 + x
  end
  else 1
