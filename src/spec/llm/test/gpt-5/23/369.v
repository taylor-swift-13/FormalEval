Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "Th    This is a sample TTetnstrinisg Jumpeto test the function           !s40ls !n 1t
" 86.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "Th    This is a sample TTetnstrinisg Jumpeto test the function           !s40ls !n 1t
") = 86%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.