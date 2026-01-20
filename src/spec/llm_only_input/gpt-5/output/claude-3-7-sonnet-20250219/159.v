Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Definition eat_spec (number need remaining : nat) (result : list nat) : Prop :=
  0 <= number <= 1000 /\
  0 <= need <= 1000 /\
  0 <= remaining <= 1000 /\
  (if Nat.leb need remaining
   then result = [(number + need)%nat; (remaining - need)%nat]
   else result = [(number + remaining)%nat; 0]).

Example eat_spec_test :
  eat_spec 5 6 10 [11; 4].
Proof.
  unfold eat_spec.
  split; [lia|].
  split; [lia|].
  split; [lia|].
  simpl.
  reflexivity.
Qed.