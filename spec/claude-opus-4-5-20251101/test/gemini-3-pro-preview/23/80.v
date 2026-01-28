Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_case1 : strlen_spec "The quick brown f ox jumps over the lazy" 40.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.