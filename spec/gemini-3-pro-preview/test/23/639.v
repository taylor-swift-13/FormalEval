Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown Fox oJutesttmps Over The BrownLazy DogmCV" 62.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.