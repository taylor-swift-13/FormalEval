Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_testing: strlen_spec "Testing testing 123" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_testing_Z: Z.of_nat (String.length "Testing testing 123") = 19%Z.
Proof.
  simpl.
  reflexivity.
Qed.