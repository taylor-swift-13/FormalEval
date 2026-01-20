Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition multiply_spec (a b result : Z) : Prop :=
  result = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_spec_test :
  multiply_spec (nth 0 ([148%Z; 412%Z]) 0%Z) (nth 1 ([148%Z; 412%Z]) 0%Z) 16%Z.
Proof.
  unfold multiply_spec.
  vm_compute.
  reflexivity.
Qed.