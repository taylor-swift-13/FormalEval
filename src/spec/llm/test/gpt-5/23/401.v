Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "This is a sample string    This is a sampl            eto string to LqNCZAtmThfGeeTeqorZJum5ymb0lsmtopsest the func Theon           to test the function" 152.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "This is a sample string    This is a sampl            eto string to LqNCZAtmThfGeeTeqorZJum5ymb0lsmtopsest the func Theon           to test the function") = 152%Z.
Proof.
  simpl.
  reflexivity.
Qed.