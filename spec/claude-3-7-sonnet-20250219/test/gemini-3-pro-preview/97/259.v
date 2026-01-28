Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec (a b : Z) (res : Z) : Prop :=
  let unit_digit_a := Z.abs a mod 10 in
  let unit_digit_b := Z.abs b mod 10 in
  res = unit_digit_a * unit_digit_b.

Example test_multiply_spec: multiply_spec 6788 (-123457) 56.
Proof.
  unfold multiply_spec.
  (* The goal becomes 56 = (Z.abs 6788 mod 10) * (Z.abs (-123457) mod 10) *)
  (* Since all values are concrete integers, we can compute the result directly. *)
  reflexivity.
Qed.