Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Definition eat_spec (number need remaining : nat) (result : list nat) : Prop :=
  0 <= number <= 1000 /\
  0 <= need <= 1000 /\
  0 <= remaining <= 1000 /\
  (if Nat.leb need remaining
   then result = [(number + need)%nat; (remaining - need)%nat]
   else result = [(number + remaining)%nat; 0]).

Example test_eat_case1 : eat_spec 5 6 10 [11; 4].
Proof.
  unfold eat_spec.
  repeat split; try lia.
  simpl. reflexivity.
Qed.