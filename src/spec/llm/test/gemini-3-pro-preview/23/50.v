Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["The quick brzown fox sjumps over the leazy Thisis is aaracter dog"], output = 65 *)
Example test_strlen_complex : strlen_spec "The quick brzown fox sjumps over the leazy Thisis is aaracter dog" 65.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.