Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example test_is_equal_to_sum_even_4 : is_equal_to_sum_even_spec 4 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intro H. discriminate H.
  - intro H. destruct H as [H1 H2]. lia.
Qed.