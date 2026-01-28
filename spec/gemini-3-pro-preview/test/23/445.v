Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukDogickn"], output = 60 *)
Example test_strlen_complex : strlen_spec "sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukDogickn" 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.