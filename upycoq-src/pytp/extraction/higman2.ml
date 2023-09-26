
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

type letter =
| A
| B

type word = letter list

type l =
| L0 of word * word list
| L1 of word * word list * l

type good =
| Good0 of word list * word * l
| Good1 of word list * word * good

type bar =
| Bar1 of word list * good
| Bar2 of word list * (word -> bar)

(** val higman : bar **)

let higman =
  failwith "AXIOM TO BE REALIZED"

(** val l_idx : (nat -> word) -> word -> word list -> l -> nat **)

let rec l_idx f w _ = function
| L0 (_, ws) -> length ws
| L1 (_, ws, l0) -> l_idx f w ws l0

(** val good_idx : (nat -> word) -> word list -> good -> (nat, nat) sigT **)

let rec good_idx f _ = function
| Good0 (ws, w, l0) -> ExistT ((l_idx f w ws l0), (length ws))
| Good1 (ws, _, g) -> good_idx f ws g

(** val bar_idx : (nat -> word) -> word list -> bar -> (nat, nat) sigT **)

let rec bar_idx f _ = function
| Bar1 (ws, g) -> good_idx f ws g
| Bar2 (ws, b) -> let w = f (length ws) in bar_idx f (Cons (w, ws)) (b w)

(** val higman_idx : (nat -> word) -> (nat, nat) sigT **)

let higman_idx f =
  bar_idx f Nil higman
