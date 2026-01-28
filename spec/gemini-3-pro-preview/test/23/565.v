Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["fuwiw1thstricQukicknnc"], output = 22 *)
Example test_strlen_custom : strlen_spec "fuwiw1thstricQukicknnc" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.