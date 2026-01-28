Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 sTtTheTer1ng wtest5ymb0lse !n 1t
Jum5ymb0lsmfunct ion" 63.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.