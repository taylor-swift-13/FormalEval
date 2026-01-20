Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCV" 77.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "MNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCV") = 77%Z.
Proof.
  simpl.
  reflexivity.
Qed.