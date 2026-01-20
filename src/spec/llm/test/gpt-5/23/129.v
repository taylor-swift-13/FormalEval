Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_spaces: strlen_spec "            " 12.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_spaces_Z: Z.of_nat (String.length "            ") = 12%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.