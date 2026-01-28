Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Th!s 1s w1This is a sample sstrintog ton test the functiont4 str1str1ngng w1th 5ymb0ls !n 1t" 92.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.