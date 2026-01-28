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

Example test_case : problem_5_spec [5; 7] [5; 3; 7] 3.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      assert (i = 0 \/ i = 1 \/ i = 2)%nat as [H0 | [H1 | H2]] by lia.
      * subst i. split.
        -- intros _. reflexivity.
        -- unfold Nat.Odd. intros [k Hk]. lia.
      * subst i. split.
        -- unfold Nat.Even. intros [k Hk]. lia.
        -- intros _. reflexivity.
      * subst i. split.
        -- intros _. reflexivity.
        -- unfold Nat.Odd. intros [k Hk]. lia.
Qed.