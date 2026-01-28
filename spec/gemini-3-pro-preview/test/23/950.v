Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["\nzTTBrownismbUmvrKpesBrMNhqThe\nTh!s 1s 4 str1str1ngng w1th 5ymb0lDogmVCVBBrownLazyLazy  s !n 1tBrow\n"], output = 100 *)
Example test_strlen_complex : strlen_spec "
zTTBrownismbUmvrKpesBrMNhqThe
Th!s 1s 4 str1str1ngng w1th 5ymb0lDogmVCVBBrownLazyLazy  s !n 1tBrow
" 100.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.