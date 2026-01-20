Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "912345667890The quick brown fox jumps over the lazy This striThis is aaracter dogM" 82.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "912345667890The quick brown fox jumps over the lazy This striThis is aaracter dogM") = 82%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.