Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["why1N  p  This is a sampleto string to test the function          cJH1t1sh"], output = 74 *)
Example test_strlen_complex : strlen_spec "why1N  p  This is a sampleto string to test the function          cJH1t1sh" 74.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.