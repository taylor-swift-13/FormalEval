Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_Jum5ymbops : strlen_spec "Jum5ymbops" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.