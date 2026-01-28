Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 81 81 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - (* Left to Right: true = true -> exists k, ... *)
    intros _.
    exists 1%nat.
    simpl.
    reflexivity.
  - (* Right to Left: (exists k, ...) -> true = true *)
    intros _.
    reflexivity.
Qed.