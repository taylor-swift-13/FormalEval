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

Example test_case : problem_5_spec [0; 0; 0] [0; 8; 0; 8; 0] 8.
Proof.
  unfold problem_5_spec.
  split.
  - (* Case: input = [] -> output = [] *)
    intros H_nil.
    discriminate H_nil.
  - (* Case: Non-empty input constraints *)
    intros n Hlen Hn.
    simpl in Hlen.
    assert (n = 3%nat) by lia.
    subst n.
    split.
    + (* length output *)
      simpl. reflexivity.
    + (* elements check *)
      intros i Hi.
      simpl in Hi.
      split.
      * (* Even case *)
        intros Heven.
        destruct i as [|i].
        { simpl. reflexivity. }
        destruct i as [|i].
        { destruct Heven as [k Hk]. lia. }
        destruct i as [|i].
        { simpl. reflexivity. }
        destruct i as [|i].
        { destruct Heven as [k Hk]. lia. }
        destruct i as [|i].
        { simpl. reflexivity. }
        lia.
      * (* Odd case *)
        intros Hodd.
        destruct i as [|i].
        { destruct Hodd as [k Hk]. lia. }
        destruct i as [|i].
        { simpl. reflexivity. }
        destruct i as [|i].
        { destruct Hodd as [k Hk]. lia. }
        destruct i as [|i].
        { simpl. reflexivity. }
        destruct i as [|i].
        { destruct Hodd as [k Hk]. lia. }
        lia.
Qed.