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

Example test_case_2 : problem_33_spec [2%Z; 3%Z; 7%Z; 8%Z; 9%Z; 10%Z; 9%Z]
                                        [2%Z; 3%Z; 7%Z; 8%Z; 9%Z; 10%Z; 9%Z].
Proof.
  unfold problem_33_spec.
  split.
  { apply Permutation_refl. }
  split.
  { intros i Hlen Hmod.
    destruct i as [| [| [| [| [| [| i]]]]]]].
    - simpl. lia.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. lia.
    - simpl. lia.
    - simpl. lia.
    - simpl. lia. }
  split.
  { intros i j [Hlen_i [Hlen_j [Hmod_i [Hmod_j Hlt]]]].
    destruct i as [| [| [| [| [| [| i]]]]]]].
    - destruct j as [| [| [| [| [| [| j]]]]]]].
      + lia.
      + simpl. lia.
      + simpl. lia.
      + simpl. lia.
      + simpl. lia.
      + simpl. lia.
      + simpl. lia.
    - simpl in Hmod_i. lia.
    - simpl in Hmod_i. lia.
    - simpl in Hmod_i. lia.
    - simpl in Hmod_i. lia.
    - simpl in Hmod_i. lia.
    - simpl in Hmod_i. lia.
    - simpl in Hmod_i. lia.
  }
Qed.