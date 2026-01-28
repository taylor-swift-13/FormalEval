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

Example test_case : problem_5_spec [2; 3] [2; 1; 3] 1.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case: input = [] -> output = [] *)
    intros H_input_nil.
    discriminate H_input_nil.
  - (* Case: Non-empty input constraints *)
    intros n H_len H_n_ge_1.
    simpl in H_len.
    subst n.
    split.
    + (* length output *)
      simpl. reflexivity.
    + (* Element-wise check *)
      intros i H_i_bound.
      destruct i as [|i].
      * (* i = 0 *)
        split.
        -- intros _. simpl. reflexivity.
        -- intros H_odd. destruct H_odd as [k Hk]. lia.
      * destruct i as [|i].
        -- (* i = 1 *)
           split.
           ++ intros H_even. destruct H_even as [k Hk]. lia.
           ++ intros _. simpl. reflexivity.
        -- destruct i as [|i].
           ++ (* i = 2 *)
              split.
              ** intros _. simpl. reflexivity.
              ** intros H_odd. destruct H_odd as [k Hk]. lia.
           ++ (* i >= 3 *)
              lia.
Qed.