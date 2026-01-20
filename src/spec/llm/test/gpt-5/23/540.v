Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "ywwtensLazy    This is a samQuaOverickple TTetnstrinisg to test the function           " 87.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "ywwtensLazy    This is a samQuaOverickple TTetnstrinisg to test the function           ") = 87%Z.
Proof.
  simpl.
  reflexivity.
Qed.