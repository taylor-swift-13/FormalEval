Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec (String.append "of" (String (Ascii.ascii_of_nat 10) "foivfe")) 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length (String.append "of" (String (Ascii.ascii_of_nat 10) "foivfe"))) = 9%Z.
Proof.
  simpl.
  reflexivity.
Qed.