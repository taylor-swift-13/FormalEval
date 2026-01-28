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

Example problem_5_pre_case_nonempty: problem_5_pre [5%Z; 7%Z] [5%Z; 3%Z; 7%Z].
Proof.
  unfold problem_5_pre.
  exact I.
Qed.

Example problem_5_spec_case_nonempty: problem_5_spec [5%Z; 7%Z] [5%Z; 3%Z; 7%Z] 3%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros n Hlen Hpos.
    simpl in Hlen. symmetry in Hlen. subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      destruct i as [|i'].
      * split.
        -- intros Heven. simpl. reflexivity.
        -- intros Hodd. exfalso. destruct Hodd as [k Hk]. lia.
      * destruct i' as [|i''].
        -- split.
           --- intros Heven. exfalso. destruct Heven as [k Hk]. lia.
           --- intros Hodd. simpl. reflexivity.
        -- destruct i'' as [|i'''].
           --- split.
               ---- intros Heven. simpl. reflexivity.
               ---- intros Hodd. exfalso. destruct Hodd as [k Hk]. lia.
           --- exfalso. lia.
Qed.