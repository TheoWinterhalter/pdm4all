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

type decode_pre (code : Type0) =
  code -> Type0

let bind_code #a (ac : Type0) (bc : a -> Type0) : Type0 =
  (** This route also doesn't work because a : Type u#a
      so the whole thing lives in Type u#a and not u#0.
      This is a problem because we're going to want u#(max a b).
  **)
  admit ()

(** Computation monad **)

noeq
type m #code (#dc : decode_pre code) (a : Type u#a) : Type u#a =
| Ret : a -> m #code #dc a
| Req : c:code -> (dc c -> m #code #dc a) -> m #code #dc a
| Read : (int -> m #code #dc a) -> m #code #dc a
| Write : int -> m #code #dc a -> m #code #dc a

(* let m_bind #ac #ad #bc #bd #a #b (c : m #ac #ad a) (f : (x:a -> m #(bc x) #(bd x) b)) : m b =
  admit () *)
