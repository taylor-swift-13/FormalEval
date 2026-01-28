Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_str1nb0lse : strlen_spec "str1nb0lse" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.