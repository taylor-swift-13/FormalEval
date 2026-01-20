Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_empty : strlen_spec "" 0.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.