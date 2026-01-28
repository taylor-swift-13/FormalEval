Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "This is a sample string    This is a sampl            eto string to test thLaàèìòùáéíóúùýâê   

  1s  îôûãñõäëïöüÿçQFoQxukyickythe function" 166.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.