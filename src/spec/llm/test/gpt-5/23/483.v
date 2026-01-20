Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sample: strlen_spec "sJTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
um5ymb0lsmfunctionJummtop    This is a sample sttotherintg to test the function      QuaOverick     s" 147.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sample_Z: Z.of_nat (String.length "sJTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
um5ymb0lsmfunctionJummtop    This is a sample sttotherintg to test the function      QuaOverick     s") = 147%Z.
Proof.
  simpl.
  reflexivity.
Qed.