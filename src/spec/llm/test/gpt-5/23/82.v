Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_abcdeflghijklmnopqrstuvwxyz: strlen_spec "abcdeflghijklmnopqrstuvwxyz" 27.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_abcdeflghijklmnopqrstuvwxyz_Z: Z.of_nat (String.length "abcdeflghijklmnopqrstuvwxyz") = 27%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.