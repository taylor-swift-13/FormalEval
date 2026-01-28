Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> 1 <= n ->
      length output = 2 * n - 1 /\
      forall i : nat, i < 2 * n - 1 ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_case_2 : problem_5_spec [5%Z; 7%Z] [5%Z; 2%Z; 7%Z] 2%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hge.
    simpl in Hlen.
    split.
    + simpl. lia.
    + intros i Hi.
      assert (n = 2) by lia.
      subst n.
      simpl in Hi.
      split.
      * intros Heven.
        destruct i as [|[|[|i']]].
        -- simpl. reflexivity.
        -- inversion Heven. lia.
        -- simpl. reflexivity.
        -- lia.
      * intros Hodd.
        destruct i as [|[|[|i']]].
        -- inversion Hodd. lia.
        -- simpl. reflexivity.
        -- inversion Hodd. destruct H as [k Hk]. lia.
        -- lia.
Qed.