Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "    This is a sample sttotherintg to test the funcstricQukickntion          " 76.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.