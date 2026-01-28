Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_Juom5ymbops : strlen_spec "Juom5ymbops" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.