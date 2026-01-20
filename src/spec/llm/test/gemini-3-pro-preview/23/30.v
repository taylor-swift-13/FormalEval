Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog" 69.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.