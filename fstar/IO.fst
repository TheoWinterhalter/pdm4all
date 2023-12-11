(** Simple IO partial DM

  For this version, we stick the preconditions as a parameter of the monad and
  not in the data itself. This way, it can still live in the lowest universe.

  TODO: For now, we only deal with a free monadic Pure, IO to come later.

**)

module IO

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics
open FStar.Classical
open FStar.Monotonic.Pure

(** Positions in the free monad **)

type position =
| Root
| PReq : position -> position

(** Precondition decoding **)

type decode_pre =
  position -> Type0

let post_req (dc : decode_pre) : decode_pre =
  fun pos -> dc (PReq pos)

(** Computation monad **)

noeq
type m (dc : decode_pre) (a : Type u#a) : Type u#a =
| Ret : a -> m dc a
| Req : (squash (dc Root) -> m (post_req dc) a) -> m dc a
(* | Read : (int -> m #code #dc a) -> m #code #dc a
| Write : int -> m #code #dc a -> m #code #dc a *)

(** Positions and preconditions **)

let rec pos_in #a #dc (pos : position) (u : m dc a) =
  match pos, u with
  | Root, _ -> True
  | PReq p, Req k -> forall (h : dc Root). p `pos_in` (k ())
  | _, _ -> False

let rec ret_in #a #dc (pos : position) (u : m dc a) =
  match pos, u with
  | _, Ret x -> True
  | PReq p, Req k -> dc Root /\ p `ret_in` (k ())
  | _, _ -> False

let rec ret_val #a #dc pos (u : m dc a) :
  Pure a (requires pos `ret_in` u) (ensures fun _ -> True)
= match pos, u with
  | _, Ret x -> x
  | PReq p, Req k -> ret_val p (k ())

let rec nextpos #a #dc pos (u : m dc a) :
  Pure position (requires pos `ret_in` u) (ensures fun _ -> True)
= match pos, u with
  | _, Ret x -> pos
  | PReq p, Req k -> nextpos p (k ())

let ret_decode : decode_pre =
  fun _ -> True

let bind_decode (#a : Type u#a) (ad : decode_pre) (u : m ad a) (bd : a -> decode_pre) :
  decode_pre
= fun pos ->
    (pos `pos_in` u ==> ad pos) /\
    (pos `ret_in` u ==> bd (ret_val pos u) (nextpos pos u))

let req_decode (pre : Type0) : decode_pre =
  fun _ -> pre

let m_ret #a (x : a) : m ret_decode a =
  Ret x

let dle (d e : decode_pre) =
  forall pos. e pos ==> d pos

(* Not very elegant to traverse the whole term for a noop *)
let rec m_lift_dec #a #dec #dec' (u : m dec a) :
  Pure (m dec' a) (requires dec `dle` dec') (ensures fun _ -> True)
= match u with
  | Ret x -> Ret x
  | Req k -> Req (fun z -> m_lift_dec (k ()))

let m_lift #a #b #ad (#bd : a -> _) (#x : a) (fx : m (bd x) b) :
  m (bind_decode ad (Ret x) bd) b =
  m_lift_dec fx

(* Quite bad that we need to lift everywhere *)
let rec m_bind (#a : Type u#a) (#b : Type u#b) #ad (#bd : a -> decode_pre)
  (u : m ad a) (f : (x:a -> m (bd x) b)) :
  m (bind_decode ad u bd) b
= match u with
  | Ret x -> m_lift (f x)
  | Req k -> Req (fun z -> m_lift_dec (m_bind (k ()) f))

let m_req (p : Type0) : m (req_decode p) (squash p) =
  Req (fun h -> Ret h)

(** Specification monad **)

type event =
| ERead : int -> event
| EWrite : int -> event

type trace = list event

let hist_append (tr : trace) (hist : trace) : trace =
  tr @ rev hist

let wpre = trace -> Type0
let wpost a = trace -> a -> Type0

let wp a = wpost a -> wpre

unfold
let _wle #a (w1 w2 : wp a) =
  forall post hist. w2 post hist ==> w1 post hist

let wle #a (w1 w2 : wp a) =
  _wle w1 w2

unfold
let _w_return #a (x : a) : wp a =
  fun post hist -> post [] x

let w_return #a (x : a) : wp a =
  _w_return x

unfold
let _w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  fun post hist -> w (fun tr x -> wf x post (hist_append tr hist)) hist

let w_bind #a #b (w : wp a) (wf : a -> wp b) : wp b =
  _w_bind w wf

let w_req (p : Type0) : wp (squash p) =
  fun post hist -> p /\ post [] (Squash.get_proof p)

(** Effect observation **)

let rec theta #ad #a (u : m ad a) : wp a =
  match u with
  | Ret x -> w_return x
  | Req k -> w_bind (w_req (ad Root)) (fun x -> theta (k ()))

(** Dijkstra monad **)

let dm a ad (w : wp a) =
  c : m ad a { theta c `wle` w }

let d_ret #a (x : a) : dm a ret_decode (w_return x) =
  m_ret x

let theta_bind (#a : Type u#a) (#b : Type u#b) #ad (#bd : a -> _)
  (u : m ad a) (f : (x : a) -> m (bd x) b) :
  Lemma (theta (m_bind u f) `wle` w_bind (theta u) (fun x -> theta (f x)))
= admit ()

let d_bind (#a : Type u#a) (#b : Type u#b) #ad (#bd : a -> _) #w (#wf : a -> wp b)
  (u : dm a ad w) (f : (x : a) -> dm b (bd x) (wf x)) :
  dm b _ (w_bind w wf) =
  theta_bind u f ;
  assume (theta (m_bind u f) `wle` w_bind w wf) ;
  m_bind u f

let d_req (p : Type0) : dm (squash p) _ (w_req p) =
  m_req p

let d_subcomp #a #ad1 #ad2 #w1 #w2 (u : dm a ad1 w1) :
  Pure (dm a ad2 w2) (requires ad1 `dle` ad2 /\ w1 `wle` w2) (ensures fun _ -> True)
= admit () ;
  m_lift_dec u

let w_if_then_else #a (w1 w2 : wp a) (b : bool) : wp a =
  fun post hist -> (b ==> w1 post hist) /\ (~ b ==> w2 post hist)

(* TODO: Probably we need an if on decoding functions. *)
let if_then_else (a : Type) #ad (w1 w2 : wp a) (f : dm a ad w1) (g : dm a ad w2) (b : bool) : Type =
  dm a ad (w_if_then_else w1 w2 b)

let elim_pure #a #w (f : unit -> PURE a w) :
  Pure
    a
    (requires w (fun _ -> True))
    (ensures fun r -> forall post. w post ==> post r)
= elim_pure_wp_monotonicity_forall () ;
  f ()

unfold
let wlift #a (w : pure_wp a) : wp a =
  fun post hist -> w (post [])

let as_requires_wlift #a (w : pure_wp a) :
  Lemma (forall post hist. wlift w post hist ==> as_requires w)
= assert (forall post (x : a). post x ==> True) ;
  elim_pure_wp_monotonicity w ;
  assert (forall post. w post ==> w (fun _ -> True)) ;
  assert (forall post. (True ==> w post) ==> w (fun _ -> True))

let lift_pure (a : Type) (w : pure_wp a) (f:(eqtype_as_type unit -> PURE a w)) : dm a _ (wlift w) =
  as_requires_wlift w ;
  d_bind #_ #_ #_ #_ #_ #(fun _ -> w_return (elim_pure #a #w f)) (d_req (as_requires w)) (fun _ ->
    let r = elim_pure #a #w f in
    let r' : dm a _ (w_return r) = d_ret r in
    r'
  )

(** Recast return and bind so that they have effect-friendly types **)

let ret a (x : a) : dm a _ (_w_return x) =
  d_ret x

let bind a b ad bd w wf u f : dm b _ (_w_bind w wf) =
  d_bind #a #b #ad #bd #w #wf u f

let subcomp a ad1 ad2 w1 w2 (c : dm a ad1 w1) :
  Pure (dm a ad2 w2) (requires ad1 `dle` ad2 /\ w1 `_wle` w2) (ensures fun _ -> True)
= d_subcomp c

(** Effect **)

total
reifiable
reflectable
effect {
  IOw (a : Type) (ad : decode_pre) (w : wp a)
  with {
    repr         = dm ;
    return       = ret ;
    bind         = bind ;
    subcomp      = subcomp ;
    if_then_else = if_then_else
  }
}
