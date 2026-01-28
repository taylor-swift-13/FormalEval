Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_newline : strlen_spec "abcdefghijklmnopq1234 This striThis is a long string that has many characters in itng has a 
 newline character5rstuvwxyz" 121.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.