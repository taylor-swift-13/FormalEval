Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "MNhqThe CuQuicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV" 89.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "MNhqThe CuQuicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV") = 89%Z.
Proof.
  simpl.
  reflexivity.
Qed.