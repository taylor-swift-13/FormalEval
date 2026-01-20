Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLaLazy z zyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1ts"], output = 125 *)
Example test_strlen_custom : strlen_spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLaLazy z zyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1ts" 125.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.