Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "MNhqThe Quick Brown Fox Jumps Over The BrownLazy DogmCrV" 56.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "MNhqThe Quick Brown Fox Jumps Over The BrownLazy DogmCrV") = 56%Z.
Proof.
  simpl.
  reflexivity.
Qed.