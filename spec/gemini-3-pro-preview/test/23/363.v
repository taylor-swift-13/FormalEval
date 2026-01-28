Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["   \n   \n\nBrownrown"], output = 18 *)
Example test_strlen_complex : strlen_spec "   
   

Brownrown" 18.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.