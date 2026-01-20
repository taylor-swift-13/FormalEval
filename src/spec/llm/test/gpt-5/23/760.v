Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_CQuDogmCVnsampBrownleLazyick: strlen_spec "CQuDogmCVnsampBrownleLazyick" 28.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_CQuDogmCVnsampBrownleLazyick_Z: Z.of_nat (String.length "CQuDogmCVnsampBrownleLazyick") = 28%Z.
Proof.
  simpl.
  reflexivity.
Qed.