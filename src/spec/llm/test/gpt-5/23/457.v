Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition crlf : string := String.String (Ascii.ascii_of_nat 13) (String.String (Ascii.ascii_of_nat 10) String.EmptyString).

Example strlen_spec_crlf: strlen_spec crlf 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_crlf_Z: Z.of_nat (String.length crlf) = 2%Z.
Proof.
  simpl.
  reflexivity.
Qed.