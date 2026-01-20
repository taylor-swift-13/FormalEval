Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case1: strlen_spec "MNhqThe CQuick Brown Fox oJumps Over The BrownLazy DogmCV" 57.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case1_Z: Z.of_nat (String.length "MNhqThe CQuick Brown Fox oJumps Over The BrownLazy DogmCV") = 57%Z.
Proof.
  simpl.
  reflexivity.
Qed.