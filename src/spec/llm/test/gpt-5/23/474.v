Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition test_str : string :=
  "Th    This iTh!s 1s RL4 str1ng wtest5ymb0l !n 1t" ++ nl ++
  "s a sample TTetnstrinisg Jumpet   " ++ nl ++
  "" ++ nl ++
  "wtest5ymb40ls    t" ++ nl.

Example strlen_spec_test: strlen_spec test_str 104.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length test_str) = 104%Z.
Proof.
  simpl.
  reflexivity.
Qed.