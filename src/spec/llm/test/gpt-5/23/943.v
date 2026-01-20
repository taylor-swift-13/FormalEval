Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition cedilla : string := String (Ascii.ascii_of_nat 231) EmptyString.

Example strlen_spec_cedilla: strlen_spec cedilla 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_cedilla_Z: Z.of_nat (String.length cedilla) = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.