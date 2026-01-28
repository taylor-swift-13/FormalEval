Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_p1s4Bnrown : strlen_spec "p1s4Bnrown" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.