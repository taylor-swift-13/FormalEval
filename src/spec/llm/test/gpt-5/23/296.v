Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition test_str : string :=
  String.append "   "
    (String.append nl
      (String.append "hy    This is a sample strinisg to test the fuunction          NcJH"
        (String.append nl "  strin"))).

Example strlen_spec_new: strlen_spec test_str 79.
Proof.
  unfold strlen_spec.
  unfold test_str.
  unfold nl.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length test_str) = 79%Z.
Proof.
  unfold test_str.
  unfold nl.
  simpl.
  reflexivity.
Qed.