Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sample: strlen_spec "    This is a sampl            eto string to test the func Theon          " 74.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sample_Z: Z.of_nat (String.length "    This is a sampl            eto string to test the func Theon          ") = 74%Z.
Proof.
  simpl.
  reflexivity.
Qed.