Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_newlines: strlen_spec (String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) EmptyString))) 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_newlines_Z: Z.of_nat (String.length (String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) EmptyString)))) = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.