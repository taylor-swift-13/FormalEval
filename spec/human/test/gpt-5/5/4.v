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

Example problem_5_pre_case_nonempty: problem_5_pre [1%Z; 2%Z; 3%Z] [1%Z; 0%Z; 2%Z; 0%Z; 3%Z].
Proof.
  unfold problem_5_pre.
  exact I.
Qed.

Example problem_5_spec_case_nonempty: problem_5_spec [1%Z; 2%Z; 3%Z] [1%Z; 0%Z; 2%Z; 0%Z; 3%Z] 0%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. inversion H.
  - intros n Hlen Hpos.
    simpl in Hlen.
    subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      split.
      * intros Heven.
        destruct Heven as [k Hk]. subst i.
        assert (k <= 2)%nat by lia.
        destruct k as [| k1].
        -- simpl. reflexivity.
        -- destruct k1 as [| k2].
           ++ simpl. reflexivity.
           ++ destruct k2 as [| k3].
              ** simpl. reflexivity.
              ** exfalso; lia.
      * intros Hodd.
        destruct Hodd as [k Hk]. subst i.
        assert (k <= 1)%nat by lia.
        destruct k as [| k1].
        -- simpl. reflexivity.
        -- destruct k1 as [| k2].
           ++ simpl. reflexivity.
           ++ exfalso; lia.
Qed.