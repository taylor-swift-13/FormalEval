Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["thrieeThe quick brown f ox jumps over the lazy dogThe quick brown fox jumps overq the lazy dog\nfour\nfive "], output = 105 *)
Example test_strlen_complex : strlen_spec ("thrieeThe quick brown f ox jumps over the lazy dogThe quick brown fox jumps overq the lazy dog" ++ String (ascii_of_nat 10) ("four" ++ String (ascii_of_nat 10) "five ")) 105.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.