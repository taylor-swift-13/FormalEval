Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Fo stgrsr1ng   This is aTh!s 1s 4 str1ng wtest5ymb0lse !n 1t\n sampleto string to test the function  n        x"], output = 110 *)
Example test_strlen_complex : strlen_spec "Fo stgrsr1ng   This is aTh!s 1s 4 str1ng wtest5ymb0lse !n 1t
 sampleto string to test the function  n        x" 110.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.