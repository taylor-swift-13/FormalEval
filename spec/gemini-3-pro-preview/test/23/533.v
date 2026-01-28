Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_sample : strlen_spec "This is a sample string Theonto test the function" 49.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.