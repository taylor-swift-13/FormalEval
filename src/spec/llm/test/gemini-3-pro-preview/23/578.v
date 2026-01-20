Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_rstn1r1n : strlen_spec "rstn1r1n" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.