Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 sstr1str1ngng w1th 5ymb0ls !n 1t" 42.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.