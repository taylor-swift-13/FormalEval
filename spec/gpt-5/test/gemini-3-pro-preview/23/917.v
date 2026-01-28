Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "   ThiBrowMNhqThe CQuick FoxJumpsBrown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z" 128.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.