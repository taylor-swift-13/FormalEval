Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b : Z) (res : Z) : Prop :=
  let unit_digit_a := Z.abs a mod 10 in
  let unit_digit_b := Z.abs b mod 10 in
  res = unit_digit_a * unit_digit_b.

Example test_multiply_spec: multiply_spec 6789 3 27.
Proof.
  unfold multiply_spec.
  (* The goal becomes 27 = (Z.abs 6789 mod 10) * (Z.abs 3 mod 10) *)
  (* Since all values are concrete integers, we can compute the result directly. *)
  reflexivity.
Qed.