Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_12345: strlen_spec "12345"%string 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_12345_Z: Z.of_nat (String.length "12345"%string) = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.