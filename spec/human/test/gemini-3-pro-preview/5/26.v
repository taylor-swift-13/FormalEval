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

Example test_example : problem_5_spec [2; 2]%Z [2; 1; 2]%Z 1%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hle.
    simpl in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2) as [-> | [-> | ->]] by lia.
      * split.
        -- intros _. reflexivity.
        -- intros Hodd. unfold Nat.Odd in Hodd. destruct Hodd. lia.
      * split.
        -- intros Heven. unfold Nat.Even in Heven. destruct Heven. lia.
        -- intros _. reflexivity.
      * split.
        -- intros _. reflexivity.
        -- intros Hodd. unfold Nat.Odd in Hodd. destruct Hodd. lia.
Qed.