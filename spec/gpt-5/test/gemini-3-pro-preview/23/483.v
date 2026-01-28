Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "sJTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
um5ymb0lsmfunctionJummtop    This is a sample sttotherintg to test the function      QuaOverick     s" 147.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.