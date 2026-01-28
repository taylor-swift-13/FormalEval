Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "This is ao sample starintog ton test the function" 49.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.