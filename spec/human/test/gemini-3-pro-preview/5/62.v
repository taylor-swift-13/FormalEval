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

Example test_case : problem_5_spec [2; 3; 4] [2; 5; 3; 5; 4] 5.
Proof.
  unfold problem_5_spec.
  split.
  - intros H.
    discriminate.
  - intros n Hlen Hn.
    simpl in Hlen.
    subst n.
    split.
    + reflexivity.
    + intros i Hi.
      simpl in Hi.
      destruct i as [| i].
      * (* i = 0 *)
        split.
        -- intros _. simpl. reflexivity.
        -- intros Hodd. inversion Hodd. lia.
      * destruct i as [| i].
        -- (* i = 1 *)
           split.
           ++ intros Heven. inversion Heven. lia.
           ++ intros _. simpl. reflexivity.
        -- destruct i as [| i].
           ++ (* i = 2 *)
              split.
              ** intros _. simpl. reflexivity.
              ** intros Hodd. inversion Hodd. lia.
           ++ destruct i as [| i].
              ** (* i = 3 *)
                 split.
                 --- intros Heven. inversion Heven. lia.
                 --- intros _. simpl. reflexivity.
              ** destruct i as [| i].
                 --- (* i = 4 *)
                     split.
                     +++ intros _. simpl. reflexivity.
                     +++ intros Hodd. inversion Hodd. lia.
                 --- (* i >= 5 *)
                     lia.
Qed.