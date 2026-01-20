Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_CQuticJumpsk: strlen_spec "CQuticJumpsk"%string 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_CQuticJumpsk_Z: Z.of_nat (String.length "CQuticJumpsk"%string) = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.