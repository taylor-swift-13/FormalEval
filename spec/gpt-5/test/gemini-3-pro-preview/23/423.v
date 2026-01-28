Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec " àèìòùáéíóúýâêîôiwTish!!1thûãñõäëïöüÿç  

wtest5ymb40ls    " 85.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.