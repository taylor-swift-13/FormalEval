Require Import ZArith.
Require Import List.

Import ListNotations.
Open Scope Z_scope.

Definition multiply_spec (a b prod : Z) : Prop :=
  prod = Z.mul (Z.modulo (Z.abs a) 10%Z) (Z.modulo (Z.abs b) 10%Z).

Example multiply_spec_test :
  let input := [-123458%Z; -10%Z] in
  multiply_spec (nth 0 input 0%Z) (nth 1 input 0%Z) 0%Z.
Proof.
  unfold multiply_spec.
  vm_compute.
  reflexivity.
Qed.