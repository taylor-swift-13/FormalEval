Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_sentence : strlen_spec "The quick brzown fox jumps over the leazy Thisis is aaracter dog" 64.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.