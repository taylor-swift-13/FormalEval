Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "one
twot
thrThis is a long string that has  many characters in itee
four
five" 77.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.