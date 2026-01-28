Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec " This striThis is a long string that has many characters in itng has a 
 newline character" 90.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.