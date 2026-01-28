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

Example test_case : problem_5_spec [2; 3; 4] [2; 10000; 3; 10000; 4] 10000.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case: input = [] -> output = [] *)
    intros H.
    discriminate H.
  - (* Case: Non-empty input constraints *)
    intros n Hlen Hn.
    simpl in Hlen. subst n.
    split.
    + (* length output = 2 * 3 - 1 = 5 *)
      simpl. reflexivity.
    + (* Element-wise check *)
      intros i Hi.
      destruct i.
      * (* i = 0 *)
        split; intros Hpar.
        -- (* Even 0 *) simpl. reflexivity.
        -- (* Odd 0 *) destruct Hpar as [k Hk]. lia.
      * destruct i.
        -- (* i = 1 *)
           split; intros Hpar.
           ++ (* Even 1 *) destruct Hpar as [k Hk]. lia.
           ++ (* Odd 1 *) simpl. reflexivity.
        -- destruct i.
           ++ (* i = 2 *)
              split; intros Hpar.
              ** (* Even 2 *) simpl. reflexivity.
              ** (* Odd 2 *) destruct Hpar as [k Hk]. lia.
           ++ destruct i.
              ** (* i = 3 *)
                 split; intros Hpar.
                 --- (* Even 3 *) destruct Hpar as [k Hk]. lia.
                 --- (* Odd 3 *) simpl. reflexivity.
              ** destruct i.
                 --- (* i = 4 *)
                     split; intros Hpar.
                     +++ (* Even 4 *) simpl. reflexivity.
                     +++ (* Odd 4 *) destruct Hpar as [k Hk]. lia.
                 --- (* i >= 5 *)
                     lia.
Qed.