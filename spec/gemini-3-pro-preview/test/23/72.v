Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec ("off" ++ String (ascii_of_nat 10) "foivife") 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.