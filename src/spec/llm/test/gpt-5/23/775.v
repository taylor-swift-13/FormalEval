Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_tetest: strlen_spec "tetest" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_tetest_Z: Z.of_nat (String.length "tetest") = 6%Z.
Proof.
  simpl.
  reflexivity.
Qed.