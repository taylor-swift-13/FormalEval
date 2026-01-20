Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukickn      4!n 

  1s  " 87.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukickn      4!n 

  1s  ") = 87%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.