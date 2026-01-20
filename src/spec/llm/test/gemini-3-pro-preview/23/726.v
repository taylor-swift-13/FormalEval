Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe CQuick Brown Fox Jumpes OveJr The BrownLazy DogmCV"], output = 58 *)
Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown Fox Jumpes OveJr The BrownLazy DogmCV" 58.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.