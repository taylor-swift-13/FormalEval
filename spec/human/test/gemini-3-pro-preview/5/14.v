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

Example test_case : problem_5_spec [2; 3] [2; 0; 3] 0.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. rewrite <- Hlen.
    split.
    + reflexivity.
    + intros i Hi.
      destruct i.
      * split.
        { intros _. reflexivity. }
        { intros H. inversion H. lia. }
      * destruct i.
        { split.
          { intros H. inversion H. lia. }
          { intros _. reflexivity. }
        }
        { destruct i.
          { split.
            { intros _. reflexivity. }
            { intros H. inversion H. lia. }
          }
          { lia. }
        }
Qed.