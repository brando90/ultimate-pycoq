
type __ = Obj.t

type nat =
| O
| S of nat

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

type 'dom tree =
| Leaf of 'dom
| Cons of 'dom tree * 'dom tree

type nat_tree = nat tree

val leavemult : nat_tree -> nat

type sPECIF = nat

val trivialalgo : nat_tree -> sPECIF

type kappa = nat -> __ -> sPECIF

val cpsalgo : nat_tree -> sPECIF
