Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_1seampLazyleat : strlen_spec "1seampLazyleat" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.