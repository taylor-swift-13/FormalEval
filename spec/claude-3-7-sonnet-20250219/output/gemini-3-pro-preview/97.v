Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b : Z) (res : Z) : Prop :=
  let unit_digit_a := Z.abs a mod 10 in
  let unit_digit_b := Z.abs b mod 10 in
  res = unit_digit_a * unit_digit_b.

Example test_multiply_spec: multiply_spec 148 412 16.
Proof.
  unfold multiply_spec.
  (* The goal becomes 16 = (Z.abs 148 mod 10) * (Z.abs 412 mod 10) *)
  (* Since all values are concrete integers, we can compute the result directly. *)
  reflexivity.
Qed.