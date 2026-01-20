Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string := "off" ++ String (Ascii.ascii_of_nat 10) "abcdefgjklmnopqrstuvwxyzfoivife".

Example strlen_spec_test: strlen_spec test_string 35.
Proof.
  unfold strlen_spec.
  unfold test_string.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length test_string) = 35%Z.
Proof.
  unfold test_string.
  simpl.
  reflexivity.
Qed.