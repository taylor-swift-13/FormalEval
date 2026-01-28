Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["fuwhy1N    This is a sampleto string to test the function          cJH1th"], output = 73 *)
Example test_strlen_complex : strlen_spec "fuwhy1N    This is a sampleto string to test the function          cJH1th" 73.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.