Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe Quick BrowTBrowMNhqmnrownisgmCVgn FoxJumpws Over The BrownLazy DogmCV"], output = 77 *)
Example test_strlen_complex : strlen_spec "MNhqThe Quick BrowTBrowMNhqmnrownisgmCVgn FoxJumpws Over The BrownLazy DogmCV" 77.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.