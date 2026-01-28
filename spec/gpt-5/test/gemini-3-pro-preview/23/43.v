Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_newline : strlen_spec " This striThis is a long string that has many characters in itng has a 
 neawline character" 91.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.