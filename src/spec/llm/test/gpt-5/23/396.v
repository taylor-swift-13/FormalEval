Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_o_circumflex: strlen_spec (String (Ascii.ascii_of_nat 244) EmptyString) 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_o_circumflex_Z: Z.of_nat (String.length (String (Ascii.ascii_of_nat 244) EmptyString)) = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.