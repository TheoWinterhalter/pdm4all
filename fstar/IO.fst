(** Simple IO partial DM

  For this version, we stick the preconditions as a parameter of the monad and
  not in the data itself. This way, it can still live in the lowest universe.

**)

module IO

open FStar.List.Tot
open FStar.List.Tot.Properties
open FStar.Tactics
open FStar.Classical
open FStar.Monotonic.Pure

(** Precondition stores **)

noeq
type prestore : Type u#1 =
| Triv
| PReq : pre:Type0 -> k:(pre -> prestore) -> prestore

let cur_pre (ps : prestore) : Type0 =
  match ps with
  | Triv -> True
  | PReq pre k -> pre

(* let req_k ps =
  match ps with
  | PReq pre k -> k
  | _ -> Triv *)

(** Computation monad **)

noeq
type m (a : Type u#a) (pres : prestore) : Type u#a =
| Ret : a -> m a pres
| Req : (cur_pre pres -> m a pres) -> m a pres // pres again is not ok of course
