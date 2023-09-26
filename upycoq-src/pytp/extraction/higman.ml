
type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type letter =
| A
| B

type word = letter list

(** val good_prefix : (nat -> word) -> word list **)

let good_prefix =
  failwith "AXIOM TO BE REALIZED"
