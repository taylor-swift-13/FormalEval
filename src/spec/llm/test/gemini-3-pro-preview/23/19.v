Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "The quick brown fox jumps over the lazy This striThis is a long string that has many characters in itng has a 
 newline character dog" 133.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.