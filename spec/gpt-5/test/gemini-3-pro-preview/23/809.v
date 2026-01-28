Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNhqThBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazyk BrowMNhqmn Fox Jumps OverThis  to tehst t" 115.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.