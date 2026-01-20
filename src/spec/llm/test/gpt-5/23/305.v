Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  String.append "Th!s 1s 4 stsr1ng wtest5ymb0ls !n 1t" (String (Ascii.ascii_of_nat 10) EmptyString).

Example strlen_spec_test: strlen_spec test_string 37.
Proof.
  unfold strlen_spec.
  unfold test_string.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length test_string) = 37%Z.
Proof.
  unfold test_string.
  simpl.
  reflexivity.
Qed.