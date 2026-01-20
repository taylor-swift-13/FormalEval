Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_str1ng : strlen_spec "str1ng" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.