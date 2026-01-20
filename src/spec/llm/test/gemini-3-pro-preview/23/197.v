Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["   \nhyNcJH\n  string"], output = 19 *)
Example test_strlen_complex : strlen_spec "   
hyNcJH
  string" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.