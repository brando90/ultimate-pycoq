
type __ = Obj.t

type nat =
| O
| S of nat

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

type 'dom tree =
| Leaf of 'dom
| Cons of 'dom tree * 'dom tree

type nat_tree = nat tree

(** val leavemult : nat_tree -> nat **)

let rec leavemult = function
| Leaf n1 -> n1
| Cons (t1, t2) -> mul (leavemult t1) (leavemult t2)

type sPECIF = nat

(** val trivialalgo : nat_tree -> sPECIF **)

let trivialalgo =
  leavemult

type kappa = nat -> __ -> sPECIF

(** val cpsalgo : nat_tree -> sPECIF **)

let cpsalgo =
  failwith "AXIOM TO BE REALIZED"
