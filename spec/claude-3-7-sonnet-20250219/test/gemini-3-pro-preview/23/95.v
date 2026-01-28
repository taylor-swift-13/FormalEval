Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_case1 : strlen_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5" 137.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.