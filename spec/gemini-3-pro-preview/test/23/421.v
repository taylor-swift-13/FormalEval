Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["why1N  p  This is a sampleto string to test the function          cJH1th"], output = 72 *)
Example test_strlen_complex : strlen_spec "why1N  p  This is a sampleto string to test the function          cJH1th" 72.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.