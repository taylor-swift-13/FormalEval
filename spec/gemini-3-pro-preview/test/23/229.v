Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Th!s40ls !n 1t   \n\n wwtest5ymb40ls    \n"], output = 39 *)
Example test_strlen_complex : strlen_spec "Th!s40ls !n 1t   

 wwtest5ymb40ls    
" 39.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.