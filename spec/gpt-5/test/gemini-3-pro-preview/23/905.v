Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "   ThiBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z" 120.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.