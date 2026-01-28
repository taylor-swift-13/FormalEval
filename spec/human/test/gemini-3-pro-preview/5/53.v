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

Example test_case : problem_5_spec [4; 4] [4; -5; 4] (-5).
Proof.
  unfold problem_5_spec.
  split.
  - intros Hinput.
    discriminate Hinput.
  - intros n Hlen Hn.
    simpl in Hlen.
    assert (n = 2%nat) by lia.
    subst n.
    split.
    + reflexivity.
    + intros i Hi.
      simpl in Hi.
      assert (i = 0 \/ i = 1 \/ i = 2)%nat as Hi_cases by lia.
      destruct Hi_cases as [H_i0 | [H_i1 | H_i2]]; subst i.
      * split.
        -- intros _. reflexivity.
        -- intros Hodd. exfalso. destruct Hodd as [k Hk]. lia.
      * split.
        -- intros Heven. exfalso. destruct Heven as [k Hk]. lia.
        -- intros _. reflexivity.
      * split.
        -- intros _. reflexivity.
        -- intros Hodd. exfalso. destruct Hodd as [k Hk]. lia.
Qed.