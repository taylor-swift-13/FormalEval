Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Open Scope string_scope.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_empty : strlen_spec "" 0.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.