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

Example problem_5_pre_case_nonempty: problem_5_pre [1%Z; 9%Z; 5%Z; 6%Z; 5%Z] [1%Z; 3%Z; 9%Z; 3%Z; 5%Z; 3%Z; 6%Z; 3%Z; 5%Z].
Proof.
  unfold problem_5_pre.
  exact I.
Qed.

Example problem_5_spec_case_nonempty: problem_5_spec [1%Z; 9%Z; 5%Z; 6%Z; 5%Z] [1%Z; 3%Z; 9%Z; 3%Z; 5%Z; 3%Z; 6%Z; 3%Z; 5%Z] 3%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros Hin. exfalso. discriminate Hin.
  - intros n Hlen Hpos.
    simpl in Hlen.
    subst n.
    split.
    + simpl. lia.
    + intros i Hi.
      split.
      * intros Heven.
        destruct i as [|i1].
        { simpl. reflexivity. }
        destruct i1 as [|i2].
        { destruct Heven as [j Hj]. exfalso. lia. }
        destruct i2 as [|i3].
        { simpl. reflexivity. }
        destruct i3 as [|i4].
        { destruct Heven as [j Hj]. exfalso. lia. }
        destruct i4 as [|i5].
        { simpl. reflexivity. }
        destruct i5 as [|i6].
        { destruct Heven as [j Hj]. exfalso. lia. }
        destruct i6 as [|i7].
        { simpl. reflexivity. }
        destruct i7 as [|i8].
        { destruct Heven as [j Hj]. exfalso. lia. }
        destruct i8 as [|i9].
        { simpl. reflexivity. }
        exfalso. lia.
      * intros Hodd.
        destruct i as [|i1].
        { destruct Hodd as [j Hj]. exfalso. lia. }
        destruct i1 as [|i2].
        { simpl. reflexivity. }
        destruct i2 as [|i3].
        { destruct Hodd as [j Hj]. exfalso. lia. }
        destruct i3 as [|i4].
        { simpl. reflexivity. }
        destruct i4 as [|i5].
        { destruct Hodd as [j Hj]. exfalso. lia. }
        destruct i5 as [|i6].
        { simpl. reflexivity. }
        destruct i6 as [|i7].
        { destruct Hodd as [j Hj]. exfalso. lia. }
        destruct i7 as [|i8].
        { simpl. reflexivity. }
        destruct i8 as [|i9].
        { destruct Hodd as [j Hj]. exfalso. lia. }
        exfalso. lia.
Qed.