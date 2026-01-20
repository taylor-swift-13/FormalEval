Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec (String.append "Th!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t" (String (ascii_of_nat 10) EmptyString)) 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length (String.append "Th!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t" (String (ascii_of_nat 10) EmptyString))) = 44%Z.
Proof.
  simpl.
  reflexivity.
Qed.