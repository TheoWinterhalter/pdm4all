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

(** Computation monad **)

noeq
type m (#code : Type u#a) (#dc : decode_pre code) (a : Type u#a) : Type u#a =
| Ret : a -> m #code #dc a
| Req : c:code -> (dc c -> m #code #dc a) -> m #code #dc a
| Read : (int -> m #code #dc a) -> m #code #dc a
| Write : int -> m #code #dc a -> m #code #dc a

let m_bind #a #b #ac #ad (#bc : a -> _) (#bd : a -> _) (c : m #ac #ad a) (f : (x:a -> m #(bc x) #(bd x) b)) : m #(bind_code ac bc) #(bind_decode #a #ac ad #bc bd) b =
  admit ()
