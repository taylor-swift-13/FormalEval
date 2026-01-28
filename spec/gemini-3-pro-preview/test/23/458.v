Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["why1N  p  This is a samplefunction          cJH1th"], output = 50 *)
Example test_strlen_complex : strlen_spec "why1N  p  This is a samplefunction          cJH1th" 50.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.