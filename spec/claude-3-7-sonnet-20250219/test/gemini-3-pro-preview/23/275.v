Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_case1 : strlen_spec "TTh!s40lsh!s 1s 4 str1nb0lse !n 1t
" 35.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.