Require Import ZArith.
Require Import Bool.

Local Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = andb (Z.leb 8 n) (Z.even n).

Example is_equal_to_sum_even_spec_test_76 :
  is_equal_to_sum_even_spec 76%Z true.
Proof.
  unfold is_equal_to_sum_even_spec.
  vm_compute.
  reflexivity.
Qed.