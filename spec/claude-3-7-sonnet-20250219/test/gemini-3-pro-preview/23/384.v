Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 stsr1ng wtest5ymb0TTh!s40lsh!sls !n 1t
" 49.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.