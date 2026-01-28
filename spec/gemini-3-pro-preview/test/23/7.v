Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_long : strlen_spec "This is a long string that has many characters in it" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.