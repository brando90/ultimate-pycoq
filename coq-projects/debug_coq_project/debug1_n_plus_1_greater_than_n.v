Require Import Lia.

 Theorem n_plus_1_greater_than_n:
    forall n: nat, n + 1> n.
 Proof.
 intro.
 lia.
 Qed.