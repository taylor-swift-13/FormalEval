Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = [" Th!s   \n\n 1s  "], output = 15 *)
Example test_strlen_complex : strlen_spec " Th!s   

 1s  " 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.