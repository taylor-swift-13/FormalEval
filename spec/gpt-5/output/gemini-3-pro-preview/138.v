Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = andb (Z.leb 8 n) (Z.even n).

Example test_case : is_equal_to_sum_even_spec 4 false.
Proof.
  unfold is_equal_to_sum_even_spec.
  (* Z.leb 8 4 evaluates to false because 8 > 4 *)
  (* Z.even 4 evaluates to true *)
  (* andb false true evaluates to false *)
  simpl.
  reflexivity.
Qed.