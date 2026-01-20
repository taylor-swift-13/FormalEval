Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "This is a sample string Theonto test the function" 49.
Proof.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "This is a sample string Theonto test the function") = 49%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.