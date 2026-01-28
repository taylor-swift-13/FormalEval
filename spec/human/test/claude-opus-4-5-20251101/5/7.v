Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Open Scope Z_scope.
Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> (1 <= n)%nat ->
      length output = (2 * n - 1)%nat /\
      forall i : nat, (i < 2 * n - 1)%nat ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_problem_5 : problem_5_spec [10%Z] [10%Z] 5%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen.
    split.
    + rewrite <- Hlen. simpl. lia.
    + intros i Hi.
      rewrite <- Hlen in Hi. simpl in Hi.
      assert (i = 0)%nat by lia.
      subst i.
      split.
      * intros _. simpl. reflexivity.
      * intros Hodd. inversion Hodd. lia.
Qed.