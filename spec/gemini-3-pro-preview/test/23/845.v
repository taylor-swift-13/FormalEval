Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Jumpsw1This"], output = 11 *)
Example test_strlen_Jumpsw1This : strlen_spec "Jumpsw1This" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.