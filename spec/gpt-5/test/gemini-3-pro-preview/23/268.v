Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec " àèìòùáéíóúýâêîôiwTish!1thûãñõäëïöüÿç  

wtest5ymb40ls    " 84.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.