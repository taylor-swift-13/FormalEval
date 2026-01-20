Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Ove    This is a sample    \n\n 1s  string to test the functoion          r"], output = 73 *)
Example test_strlen_complex : strlen_spec "Ove    This is a sample    

 1s  string to test the functoion          r" 73.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.