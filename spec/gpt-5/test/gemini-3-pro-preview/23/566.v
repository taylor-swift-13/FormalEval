Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_cJH1t1sh : strlen_spec "cJH1t1sh" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.