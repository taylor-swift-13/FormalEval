Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Definition problem_33_spec (input output : list Z) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 3 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 3 = 0 /\ j mod 3 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example test_case_1 : problem_33_spec [] [].
Proof.
  unfold problem_33_spec.
  split.
  { apply Permutation_refl. }
  split.
  { intros i Hlen Hmod.
    simpl in Hlen. lia. }
  { intros i j [Hlen_i [Hlen_j [Hmod_i [Hmod_j Hlt]]]].
    simpl in Hlen_i, Hlen_j. lia. }
Qed.