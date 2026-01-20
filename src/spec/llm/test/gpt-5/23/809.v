Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "MNhqThBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazyk BrowMNhqmn Fox Jumps OverThis  to tehst t" 115.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "MNhqThBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazyk BrowMNhqmn Fox Jumps OverThis  to tehst t") = 115%Z.
Proof.
  simpl.
  reflexivity.
Qed.