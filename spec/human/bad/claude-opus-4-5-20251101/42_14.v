Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example test_problem_42 : problem_42_spec [4%Z; -2%Z; -3%Z; -4%Z] [5%Z; -1%Z; -2%Z; -3%Z].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 4 (destruct i; [simpl; reflexivity |]).
    simpl in H. repeat apply Nat.succ_lt_mono in H. inversion H.
Qed.