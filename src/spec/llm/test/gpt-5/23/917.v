Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_input: strlen_spec "   ThiBrowMNhqThe CQuick FoxJumpsBrown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z" 128.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_input_Z: Z.of_nat (String.length "   ThiBrowMNhqThe CQuick FoxJumpsBrown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z") = 128%Z.
Proof.
  simpl.
  reflexivity.
Qed.