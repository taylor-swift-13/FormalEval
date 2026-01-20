Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_newline_fnunc: strlen_spec (String (Ascii.ascii_of_nat 10) ("fnunc" ++ String (Ascii.ascii_of_nat 10) EmptyString)) 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_newline_fnunc_Z: Z.of_nat (String.length (String (Ascii.ascii_of_nat 10) ("fnunc" ++ String (Ascii.ascii_of_nat 10) EmptyString))) = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.