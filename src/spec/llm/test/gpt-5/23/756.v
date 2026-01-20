Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "MNhqThe CQuicJumpsk Browno Fox Jumps Over The BrownLazy DogmCV" 62.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "MNhqThe CQuicJumpsk Browno Fox Jumps Over The BrownLazy DogmCV") = 62%Z.
Proof.
  simpl.
  reflexivity.
Qed.