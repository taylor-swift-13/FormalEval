Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Th!s 1s w1This is a sample sstrintog ton test the functiont4 str1str1ngng w1th 5ymb0ls !n 1t"], output = 92 *)
Example test_strlen_complex : strlen_spec "Th!s 1s w1This is a sample sstrintog ton test the functiont4 str1str1ngng w1th 5ymb0ls !n 1t" 92.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.