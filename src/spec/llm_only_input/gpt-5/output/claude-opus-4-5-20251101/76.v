Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example is_simple_power_spec_16_2_true : is_simple_power_spec 16%Z 2%Z true.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros _.
    exists 4%nat.
    simpl (Z.of_nat 4%nat).
    compute.
    reflexivity.
  - intros _.
    reflexivity.
Qed.