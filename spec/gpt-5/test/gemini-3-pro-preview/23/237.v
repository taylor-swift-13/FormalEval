Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "TTh!s40lsh!s 1s 4 str1ng wtest5ymb0lse !n 1t
" 45.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.