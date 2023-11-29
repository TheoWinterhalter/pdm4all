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

(** Precondition decoding **)

type decode_pre (code : Type u#a) =
  code -> Type0

(* Basically unit *)
type ret_code : Type u#a =
| Triv

let ret_decode : decode_pre ret_code =
  function
  | Triv -> True

noeq
type bind_code (#a : Type u#a) (ac : Type u#a) (bc : a -> Type u#b) : Type u#(max a b) =
| BL : ac -> bind_code #a ac bc
| BR : x:a -> bc x -> bind_code #a ac bc

let bind_decode #a #ac ad (#bc : a -> Type0) (bd : (x:a -> decode_pre (bc x))) :
  decode_pre (bind_code #a ac bc)
= function
  | BL c -> ad c
  | BR x c -> bd x c

let req_code = ret_code

let req_decode (pre : Type0) : decode_pre req_code =
  function
  | Triv -> squash pre

(** Computation monad **)

noeq
type m (#code : Type u#a) (#dc : decode_pre code) (a : Type u#a) : Type u#a =
| Ret : a -> m #code #dc a
| Req : c:code -> (dc c -> m #code #dc a) -> m #code #dc a
(* | Read : (int -> m #code #dc a) -> m #code #dc a
| Write : int -> m #code #dc a -> m #code #dc a *)

let m_ret #a (x : a) : m #ret_code #ret_decode a =
  Ret x

(* Not very elegant to traverse the whole term for a noop *)
let rec m_lift #a #b #ac #ad (#bc : a -> _) (#bd : a -> _) (#x : a) (fx : m #(bc x) #(bd x) b) :
  m #(bind_code ac bc) #(bind_decode #a #ac ad #bc bd) b =
  match fx with
  | Ret y -> Ret y
  | Req c k -> Req (BR x c) (fun z -> m_lift (k z))

let rec m_bind #a #b #ac #ad (#bc : a -> _) (#bd : a -> _) (u : m #ac #ad a) (f : (x:a -> m #(bc x) #(bd x) b)) : m #(bind_code ac bc) #(bind_decode #a #ac ad #bc bd) b =
  match u with
  | Ret x -> m_lift (f x)
  | Req c k -> Req (BL c) (fun z -> m_bind (k z) f)

let m_req (p : Type0) : m #req_code #(req_decode p) (squash p) =
  Req Triv (fun h -> Ret h)

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

(* let rec theta #ac #ad #a (u : m #ac #ad a) : wp a =
  match u with
  | Ret x -> w_return x
  | Req c k -> w_bind (w_req (ad c)) (fun x -> theta (k x)) *)
