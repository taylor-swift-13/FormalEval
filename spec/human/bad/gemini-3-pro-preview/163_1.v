Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.SetoidList.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition problem_163_pre (a b : nat) : Prop := a > 0 /\ b > 0.

Definition problem_163_spec (a b : nat) (l : list nat) : Prop :=
  (forall d : nat,
    In d l <-> (min a b <= d /\ d <= max a b /\ d < 10 /\ Nat.Even d)) /\
  Sorted le l /\
  NoDup l.

Example test_case : problem_163_spec 2 10 [2; 4; 6; 8].
Proof.
  unfold problem_163_spec.
  split.
  - (* Part 1: Correctness and Completeness *)
    intro n.
    split.
    + (* Forward: In list -> Properties *)
      intro H.
      simpl in H.
      repeat destruct H as [H | H]; subst n.
      * (* n = 2 *) repeat split; try lia. exists 1. lia.
      * (* n = 4 *) repeat split; try lia. exists 2. lia.
      * (* n = 6 *) repeat split; try lia. exists 3. lia.
      * (* n = 8 *) repeat split; try lia. exists 4. lia.
      * (* False *) contradiction.
    + (* Backward: Properties -> In list *)
      intros [Hmin [Hmax [Hlt [k Hk]]]].
      simpl in Hmin, Hmax.
      subst n.
      (* From 2 <= 2*k and 2*k < 10, we deduce 1 <= k < 5 *)
      assert (Hk_range: 1 <= k < 5) by lia.
      
      (* Exhaustive case analysis for k *)
      destruct k; [ lia | ]. (* k=0, impossible *)
      destruct k; [ simpl; left; reflexivity | ]. (* k=1 -> n=2 *)
      destruct k; [ simpl; right; left; reflexivity | ]. (* k=2 -> n=4 *)
      destruct k; [ simpl; right; right; left; reflexivity | ]. (* k=3 -> n=6 *)
      destruct k; [ simpl; right; right; right; left; reflexivity | ]. (* k=4 -> n=8 *)
      lia. (* k >= 5, impossible *)

  - (* Part 2 & 3: Sorted and NoDup *)
    split.
    + (* Sorted *)
      repeat constructor; lia.
    + (* NoDup *)
      repeat constructor; simpl; intro H; repeat destruct H as [H | H]; try lia.
Qed.