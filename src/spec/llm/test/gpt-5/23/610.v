Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "MNMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCV
hqmCV" 65.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "MNMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCV
hqmCV") = 65%Z.
Proof.
  simpl.
  reflexivity.
Qed.