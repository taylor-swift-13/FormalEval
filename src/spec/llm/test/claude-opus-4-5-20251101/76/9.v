Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 1 1 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    exists 0%nat.
    reflexivity.
  - intros _.
    reflexivity.
Qed.