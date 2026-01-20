Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "Th!s 1sr 4 str1str1ngnsg w1th 5ymb0ls !n 1t" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "Th!s 1sr 4 str1str1ngnsg w1th 5ymb0ls !n 1t") = 43%Z.
Proof.
  simpl.
  reflexivity.
Qed.