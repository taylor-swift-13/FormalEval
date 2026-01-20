Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "Fo    This is a sampleto string to test the function  n        x" 64.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "Fo    This is a sampleto string to test the function  n        x") = 64%Z.
Proof.
  simpl.
  reflexivity.
Qed.