Require Import Coq.ZArith.ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = true <-> (n >= 8 /\ n mod 2 = 0).

Example test_case_1 : is_equal_to_sum_even_spec 8 true.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - intros _.
    split.
    + lia.
    + reflexivity.
  - intros _.
    reflexivity.
Qed.