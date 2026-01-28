Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "This is ao sample starintog ton test the n" 42.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.