Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_simple_power_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> exists k : nat, Z.pow n (Z.of_nat k) = x.

Example test_is_simple_power : is_simple_power_spec 64 4 true.
Proof.
  unfold is_simple_power_spec.
  split.
  - (* Left to Right: true = true -> exists k, ... *)
    intros _.
    exists 3%nat.
    (* Simplify Z.of_nat 3 to 3 and compute 4^3 *)
    simpl. 
    reflexivity.
  - (* Right to Left: (exists k, ...) -> true = true *)
    intros _.
    reflexivity.
Qed.