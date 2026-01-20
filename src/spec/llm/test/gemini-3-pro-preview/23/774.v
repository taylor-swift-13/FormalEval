Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_long : strlen_spec "MNhqThBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazyk BrowMNhqmn Fox Jumps OverThis  to test t" 114.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.