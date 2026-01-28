Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Reals.Reals.
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
    (nth i output 0 <= nth j output 0)).

Example problem_37_test1 :
  problem_37_spec [29.192135197854643; 33.66238184288656; 29.291147603502964]
                  [29.192135197854643; 33.66238184288656; 29.291147603502964].
Proof.
  unfold problem_37_spec.
  split; [| split].
  - apply Permutation_refl.
  - intros i Hi Hodd.
    simpl in Hi.
    destruct i as [|i'].
    + simpl in Hodd. exfalso. apply Hodd. reflexivity.
    + destruct i' as [|i''].
      * simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- simpl in Hodd. exfalso. apply Hodd. reflexivity.
        -- simpl in Hi. lia.
  - intros i j [Hilen [Hjlen [Himod [Hjmod Hij]]]].
    simpl in Hilen, Hjlen.
    destruct i as [|i'].
    + destruct j as [|j'].
      * lia.
      * destruct j' as [|j''].
        -- simpl in Hjmod. discriminate.
        -- destruct j'' as [|j'''].
           ++ simpl. left. lra.
           ++ lia.
    + destruct i' as [|i''].
      * simpl in Himod. discriminate.
      * destruct i'' as [|i'''].
        -- destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** simpl in Hjmod. discriminate.
              ** destruct j'' as [|j'''].
                 --- lia.
                 --- lia.
        -- lia.
Qed.