Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec (String.append "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintog to test the function" (String (Ascii.ascii_of_nat 13) "gmCV")) 107.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length (String.append "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintog to test the function" (String (Ascii.ascii_of_nat 13) "gmCV"))) = 107%Z.
Proof.
  simpl.
  reflexivity.
Qed.