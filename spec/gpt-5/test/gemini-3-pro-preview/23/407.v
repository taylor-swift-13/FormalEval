Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Fo stgrsr1ng   This is aTh!s 1s 4 str1ng wtest5ymb0lse !n 1t
 sampleto string to test the function  n        x" 110.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.