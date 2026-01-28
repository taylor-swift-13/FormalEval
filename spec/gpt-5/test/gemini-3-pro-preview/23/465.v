Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_new : strlen_spec "Ths !nîôûãñõäëïöüÿçQFoyQxukyickythe 1t
" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.