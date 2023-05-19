Inductive my_parens : Type :=
| LeftMyParen
| RightMyParen.

Notation "<<<<" := LeftMyParen.
Notation ">>>>" := RightMyParen.
Compute LeftMyParen.
Compute RightMyParen.

Definition __hole {A:Type} (lp : my_parens) (n:nat) (v:A) (rp : my_parens) := v.



Definition square (n : nat) : nat.
Proof.
refine (__hole LeftMyParen 0 _ RightMyParen).
(* Show Proof. *)
  exact (n + n).
Defined.