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

Example problem_5_pre_case: problem_5_pre [0%Z; 0%Z; 0%Z; -1%Z] [0%Z; 7%Z; 0%Z; 7%Z; 0%Z; 7%Z; -1%Z].
Proof.
  unfold problem_5_pre.
  exact I.
Qed.

Example problem_5_spec_case: problem_5_spec [0%Z; 0%Z; 0%Z; -1%Z] [0%Z; 7%Z; 0%Z; 7%Z; 0%Z; 7%Z; -1%Z] 7%Z.
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
        destruct Heven as [k Hk].
        subst i.
        destruct k as [|k1].
        -- simpl. reflexivity.
        -- destruct k1 as [|k2].
           ++ simpl. reflexivity.
           ++ destruct k2 as [|k3].
              ** simpl. reflexivity.
              ** destruct k3 as [|k4].
                 --- simpl. reflexivity.
                 --- exfalso; lia.
      * intros Hodd.
        destruct Hodd as [k Hk].
        subst i.
        destruct k as [|k1].
        -- simpl. reflexivity.
        -- destruct k1 as [|k2].
           ++ simpl. reflexivity.
           ++ destruct k2 as [|k3].
              ** simpl. reflexivity.
              ** exfalso; lia.
Qed.