Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_case1 : strlen_spec "stgrsr1ngLqNtCZAtest" 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.