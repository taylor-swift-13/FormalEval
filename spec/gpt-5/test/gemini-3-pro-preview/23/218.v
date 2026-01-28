Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "funtThis is a sample string    This is a sampl            eto string to test the func Theon           to test the functionhec" 125.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.