Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_MNhqThe_CQuick_Brown_Fwox_Jumpes_Over_The_BrownLazey_DogmCV: strlen_spec "MNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCV" 59.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_MNhqThe_CQuick_Brown_Fwox_Jumpes_Over_The_BrownLazey_DogmCV_Z: Z.of_nat (String.length "MNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCV") = 59%Z.
Proof.
  simpl.
  reflexivity.
Qed.