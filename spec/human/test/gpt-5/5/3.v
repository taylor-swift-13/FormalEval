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

Example problem_5_pre_case_empty: problem_5_pre [2%Z; 2%Z; 2%Z] [2%Z; 2%Z; 2%Z; 2%Z; 2%Z].
Proof.
  unfold problem_5_pre.
  exact I.
Qed.

Example problem_5_spec_case_empty: problem_5_spec [2%Z; 2%Z; 2%Z] [2%Z; 2%Z; 2%Z; 2%Z; 2%Z] 2%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. exfalso. inversion H.
  - intros n Hlen Hpos.
    simpl in Hlen.
    symmetry in Hlen.
    subst n.
    split.
    + simpl. reflexivity.
    + intros i Hi.
      split.
      * intros _.
        destruct i as [|i1].
        { simpl. reflexivity. }
        destruct i1 as [|i2].
        { simpl. reflexivity. }
        destruct i2 as [|i3].
        { simpl. reflexivity. }
        destruct i3 as [|i4].
        { simpl. reflexivity. }
        destruct i4 as [|i5].
        { simpl. reflexivity. }
        exfalso; lia.
      * intros _.
        destruct i as [|i1].
        { simpl. reflexivity. }
        destruct i1 as [|i2].
        { simpl. reflexivity. }
        destruct i2 as [|i3].
        { simpl. reflexivity. }
        destruct i3 as [|i4].
        { simpl. reflexivity. }
        destruct i4 as [|i5].
        { simpl. reflexivity. }
        exfalso; lia.
Qed.