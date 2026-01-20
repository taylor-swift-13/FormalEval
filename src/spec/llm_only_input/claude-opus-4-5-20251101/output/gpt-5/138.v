Require Import ZArith.
Require Import Bool.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = andb (Z.leb 8 n) (Z.even n).

Example test_is_equal_to_sum_even : is_equal_to_sum_even_spec 4%Z false.
Proof.
  unfold is_equal_to_sum_even_spec.
  simpl.
  reflexivity.
Qed.