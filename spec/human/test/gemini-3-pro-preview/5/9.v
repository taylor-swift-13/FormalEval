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

Example test_case : problem_5_spec [1; 3; 5; 7] [1; 4; 3; 4; 5; 4; 7] 4.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case: input = [] -> output = [] *)
    intros H.
    discriminate H.
  - (* Case: Non-empty input constraints *)
    intros n Hlen Hn.
    simpl in Hlen.
    inversion Hlen. subst n.
    split.
    + (* Length check *)
      simpl. reflexivity.
    + (* Element check *)
      intros i Hi.
      destruct i as [|i].
      * (* i = 0 *)
        split.
        -- intros _. simpl. reflexivity.
        -- intros Hodd. destruct Hodd; lia.
      * destruct i as [|i].
        -- (* i = 1 *)
           split.
           ++ intros Heven. destruct Heven; lia.
           ++ intros _. simpl. reflexivity.
        -- destruct i as [|i].
           ++ (* i = 2 *)
              split.
              ** intros _. simpl. reflexivity.
              ** intros Hodd. destruct Hodd; lia.
           ++ destruct i as [|i].
              ** (* i = 3 *)
                 split.
                 --- intros Heven. destruct Heven; lia.
                 --- intros _. simpl. reflexivity.
              ** destruct i as [|i].
                 --- (* i = 4 *)
                     split.
                     +++ intros _. simpl. reflexivity.
                     +++ intros Hodd. destruct Hodd; lia.
                 --- destruct i as [|i].
                     +++ (* i = 5 *)
                         split.
                         *** intros Heven. destruct Heven; lia.
                         *** intros _. simpl. reflexivity.
                     +++ destruct i as [|i].
                         *** (* i = 6 *)
                             split.
                             ---- intros _. simpl. reflexivity.
                             ---- intros Hodd. destruct Hodd; lia.
                         *** (* i >= 7 *)
                             lia.
Qed.