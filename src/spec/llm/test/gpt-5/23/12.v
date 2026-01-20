Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_1234567890: strlen_spec ("1234567890"%string) 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_1234567890_Z: Z.of_nat (String.length ("1234567890"%string)) = 10%Z.
Proof.
  simpl.
  reflexivity.
Qed.