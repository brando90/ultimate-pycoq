
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

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

val higman : bar

val l_idx : (nat -> word) -> word -> word list -> l -> nat

val good_idx : (nat -> word) -> word list -> good -> (nat, nat) sigT

val bar_idx : (nat -> word) -> word list -> bar -> (nat, nat) sigT

val higman_idx : (nat -> word) -> (nat, nat) sigT
