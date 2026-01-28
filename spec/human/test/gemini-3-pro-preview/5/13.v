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

Example test_case : problem_5_spec [1; 9; 5; 6] [1; 3; 9; 3; 5; 3; 6] 3.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. inversion H.
  - intros n Hlen Hn.
    simpl in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      destruct i as [|i].
      { split; [intros _; reflexivity | intros [m Hm]; lia]. }
      destruct i as [|i].
      { split; [intros [m Hm]; lia | intros _; reflexivity]. }
      destruct i as [|i].
      { split; [intros _; reflexivity | intros [m Hm]; lia]. }
      destruct i as [|i].
      { split; [intros [m Hm]; lia | intros _; reflexivity]. }
      destruct i as [|i].
      { split; [intros _; reflexivity | intros [m Hm]; lia]. }
      destruct i as [|i].
      { split; [intros [m Hm]; lia | intros _; reflexivity]. }
      destruct i as [|i].
      { split; [intros _; reflexivity | intros [m Hm]; lia]. }
      lia.
Qed.