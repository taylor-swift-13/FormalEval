Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Hello,The quick brown fox jumps over the lazy Thisthree\nfour\nfiveracter dog Woo12345rld!"], output = 88 *)
Example test_strlen_complex : strlen_spec "Hello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld!" 88.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.