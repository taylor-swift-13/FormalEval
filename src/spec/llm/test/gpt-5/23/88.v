Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_multiline: strlen_spec (String.append "one" (String (Ascii.ascii_of_nat 10) (String.append "two" (String (Ascii.ascii_of_nat 10) "thrfoive")))) 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z: Z.of_nat (String.length (String.append "one" (String (Ascii.ascii_of_nat 10) (String.append "two" (String (Ascii.ascii_of_nat 10) "thrfoive"))))) = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.