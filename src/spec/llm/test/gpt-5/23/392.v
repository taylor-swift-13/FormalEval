Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "nfuntThis is a sample string    This is a sampl            eto string to test the func Theon           to test the functionheccc" 128.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length "nfuntThis is a sample string    This is a sampl            eto string to test the func Theon           to test the functionheccc") = 128%Z.
Proof.
  simpl.
  reflexivity.
Qed.