Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "This is a sample strintog ton test the function" 47.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.