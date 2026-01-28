Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["   \n\n 1s  "], output = 10 *)
Example test_strlen_case1 : strlen_spec "   

 1s  " 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.