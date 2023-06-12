(* Show proof. This command requires an open proof. It gives the proof term Coq is Building. *)

Theorem add_easy_induct_1:
forall n:nat,
  n + 0 = n.
Proof.
Show proof. 
  intros.
Show proof.
  induction n as [| n' IH].
Show proof.
  - simpl.
Show proof.
    reflexivity.
Show proof.
  - simpl.
Show proof.
    rewrite -> IH.
Show proof.
    reflexivity.
Show proof.
Qed.


Definition plus (x y : nat) : nat :=
  x + y.

Theorem plus_commutes : forall x y : nat,
  plus x y = plus y x.
Proof.
Show proof.
  intros x y.
Show proof.
  simpl.
Show proof.
  rewrite plus_comm.
Show proof.
  reflexivity.
Show proof.
Qed.
