Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th!s40ls !n 1This is a sample string    This Dàèìòù4áéíóúýâêîôûãñõäëïöüÿçgogis a samplt1t            etto string to LqNCZAtest the func Theon           to test the functi           àèìòùáéíóúýâêîQckôûãñõäëïöüÿçnt
" 265.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.