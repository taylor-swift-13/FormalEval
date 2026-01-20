Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "     str1ng 1t  The    This is a samThT    1sampLazylet 1 The    ipleOvering to test the function" 97.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.