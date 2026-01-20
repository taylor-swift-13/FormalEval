Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_example: strlen_spec "MThe quick brown fox jumps over the lazy This striThis is aaracter dogM" 71.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_example_Z: Z.of_nat (String.length "MThe quick brown fox jumps over the lazy This striThis is aaracter dogM") = 71%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.