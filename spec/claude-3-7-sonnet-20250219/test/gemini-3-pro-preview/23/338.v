Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "This is a sample string    This is a sampl            eto string to test thLaàèìòùáéíóúùýâê   

  Bro1s  îôûãñõäëïöüÿçQFoQxukyickythe function" 169.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.