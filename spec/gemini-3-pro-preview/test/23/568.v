Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["wtestm5nTheymb0ls"], output = 17 *)
Example test_strlen_complex : strlen_spec "wtestm5nTheymb0ls" 17.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.