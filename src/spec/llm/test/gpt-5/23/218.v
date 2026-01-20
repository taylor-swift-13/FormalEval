Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_empty: strlen_spec "funtThis is a sample string    This is a sampl            eto string to test the func Theon           to test the functionhec" 125.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_empty_Z: Z.of_nat (String.length "funtThis is a sample string    This is a sampl            eto string to test the func Theon           to test the functionhec") = 125%Z.
Proof.
  simpl.
  reflexivity.
Qed.