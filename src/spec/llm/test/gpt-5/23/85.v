Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_1122345: strlen_spec "1122345" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_1122345_Z: Z.of_nat (String.length "1122345") = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.