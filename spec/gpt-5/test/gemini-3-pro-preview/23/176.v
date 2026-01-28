Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "    This is a sampl            eto string to test the func Theon          " 74.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.