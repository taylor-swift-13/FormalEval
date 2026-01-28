Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Tish!  TTh!s40lsh!s 1s 4 str1ng wtest5ymb0lse !n 1t
         " 61.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.