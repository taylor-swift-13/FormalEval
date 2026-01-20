Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case1: strlen_spec "MNhqThe CQu			ick Brown func!ntionFox oJutesttmps Over The BrownLazy DogmCV"%string 75.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case1_Z: Z.of_nat (String.length "MNhqThe CQu			ick Brown func!ntionFox oJutesttmps Over The BrownLazy DogmCV"%string) = 75%Z.
Proof.
  simpl.
  reflexivity.
Qed.