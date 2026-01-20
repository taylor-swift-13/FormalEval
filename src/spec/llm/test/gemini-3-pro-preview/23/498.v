Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Fow1thF1Thisxuk" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.