Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "    This is a sampl           eto string to test the func tion          " 72.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.