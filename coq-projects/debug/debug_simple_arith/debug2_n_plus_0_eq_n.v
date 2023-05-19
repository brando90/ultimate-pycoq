Theorem add_easy_induct_1:
forall n:nat,
  n + 0 = n.
Proof.
  intros.
  induction n as [| n' IH].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IH.
    reflexivity.
Qed.