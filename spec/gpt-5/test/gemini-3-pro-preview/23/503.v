Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "   

wwtes        t    ls    Th!s 1s 4 str1ng wtest5ymb0ls !n 1t
 " 66.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.