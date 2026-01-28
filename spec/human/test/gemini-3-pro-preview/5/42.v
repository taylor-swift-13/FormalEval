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

Example test_case : problem_5_spec [3; 4] [3; 10000; 4] 10000.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. inversion Hlen. subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      simpl in Hi.
      assert (H_cases: i = 0%nat \/ i = 1%nat \/ i = 2%nat) by lia.
      destruct H_cases as [H0 | [H1 | H2]]; subst i.
      * split.
        -- intros _. simpl. reflexivity.
        -- intros Hodd. destruct Hodd as [k Hk]. lia.
      * split.
        -- intros Heven. destruct Heven as [k Hk]. lia.
        -- intros _. simpl. reflexivity.
      * split.
        -- intros _. simpl. reflexivity.
        -- intros Hodd. destruct Hodd as [k Hk]. lia.
Qed.