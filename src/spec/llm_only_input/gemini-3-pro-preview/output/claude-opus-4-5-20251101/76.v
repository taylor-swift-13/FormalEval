Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 16 2 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - (* Forward direction: true = true -> exists k, 2^k = 16 *)
    intros H.
    exists 4%nat.
    simpl.
    reflexivity.
  - (* Backward direction: (exists k, 2^k = 16) -> true = true *)
    intros H.
    reflexivity.
Qed.