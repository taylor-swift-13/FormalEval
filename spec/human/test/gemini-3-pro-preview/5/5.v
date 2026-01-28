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

Example test_example : problem_5_spec [2; 4; 6; 8]%Z [2; 1; 4; 1; 6; 1; 8]%Z 1%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H.
    discriminate H.
  - intros n Hlen Hle.
    simpl in Hlen.
    subst n.
    split.
    + reflexivity.
    + intros i Hi.
      assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6) by lia.
      destruct H as [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]].
      * split.
        -- intros _. reflexivity.
        -- intros [k Hk]. lia.
      * split.
        -- intros [k Hk]. lia.
        -- intros _. reflexivity.
      * split.
        -- intros _. reflexivity.
        -- intros [k Hk]. lia.
      * split.
        -- intros [k Hk]. lia.
        -- intros _. reflexivity.
      * split.
        -- intros _. reflexivity.
        -- intros [k Hk]. lia.
      * split.
        -- intros [k Hk]. lia.
        -- intros _. reflexivity.
      * split.
        -- intros _. reflexivity.
        -- intros [k Hk]. lia.
Qed.