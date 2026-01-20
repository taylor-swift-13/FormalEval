Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "MNhqThe CQugicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV" 89.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "MNhqThe CQugicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV") = 89%Z.
Proof.
  simpl.
  reflexivity.
Qed.