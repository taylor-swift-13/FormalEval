Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "   ThiBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z" 120.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "   ThiBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z") = 120%Z.
Proof.
  simpl.
  reflexivity.
Qed.