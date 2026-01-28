Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Fixpoint utf8_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String (Ascii _ _ _ _ _ _ false true) s' => utf8_length s'
  | String _ s' => S (utf8_length s')
  end.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = utf8_length s.

Example test_strlen_case1 : strlen_spec "àèìòùáéíBrMNhqTheóúýâêîôûãñõäëïöüÿç" 35.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.