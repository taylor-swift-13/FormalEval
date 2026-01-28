Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Open Scope R_scope.

Definition problem_37_pre (input : list R) : Prop := True.

Definition problem_37_spec (input output : list R) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0)%nat ->
    nth i output 0 = nth i input 0) /\
  (forall (i j : nat), (i < length output)%nat /\ (j < length output)%nat /\
    (i mod 2 = 0)%nat /\ (j mod 2 = 0)%nat /\ (i < j)%nat ->
    nth i output 0 <= nth j output 0).

Example test_case_37: problem_37_spec 
  [29.192135197854643%R; 33.66238184288656%R; 29.291147603502964%R] 
  [29.192135197854643%R; 33.66238184288656%R; 29.291147603502964%R].
Proof.
  unfold problem_37_spec.
  split.
  - apply Permutation_refl.
  - split.
    + intros i Hlen Hodd.
      destruct i.
      * simpl in Hodd. lia.
      * destruct i.
        -- simpl. reflexivity.
        -- destruct i.
           ++ simpl in Hodd. lia.
           ++ simpl in Hlen. lia.
    + intros i j H.
      destruct H as [Hi [Hj [Hie [Hje Hij]]]].
      destruct i.
      * destruct j.
        -- lia.
        -- destruct j.
           ++ simpl in Hje. lia.
           ++ destruct j.
              ** simpl. lra.
              ** simpl in Hj. lia.
      * destruct i.
        -- simpl in Hie. lia.
        -- destruct i.
           ++ destruct j; [lia|].
              destruct j; [lia|].
              destruct j; [lia|].
              simpl in Hj. lia.
           ++ simpl in Hi. lia.
Qed.