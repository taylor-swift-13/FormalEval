Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_3_7 : greatest_common_divisor_spec 3 7 1.
Proof.
  unfold greatest_common_divisor_spec.
  (* Z.abs 1 evaluates to 1. Z.gcd 3 7 evaluates to 1. *)
  reflexivity.
Qed.