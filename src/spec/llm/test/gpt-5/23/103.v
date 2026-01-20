Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_two_spaces: strlen_spec "  " 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_two_spaces_Z: Z.of_nat (String.length "  ") = 2%Z.
Proof.
  simpl.
  reflexivity.
Qed.