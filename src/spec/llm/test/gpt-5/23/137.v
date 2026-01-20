Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_single_digit: strlen_spec "4"%string 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_single_digit_Z: Z.of_nat (String.length "4"%string) = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.