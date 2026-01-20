Require Import ZArith.
Require Import Znumtheory.
Require Import List.

Open Scope Z_scope.
Import ListNotations.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_direct :
  greatest_common_divisor_spec 3%Z 7%Z 1%Z.
Proof.
  unfold greatest_common_divisor_spec.
  vm_compute.
  reflexivity.
Qed.

Example gcd_test_from_list :
  greatest_common_divisor_spec (nth 0 [3%Z; 7%Z] 0%Z)
                               (nth 1 [3%Z; 7%Z] 0%Z)
                               1%Z.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  vm_compute.
  reflexivity.
Qed.