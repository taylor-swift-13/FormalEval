Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Definition problem_37_pre (input : list Z) : Prop := True.

Definition problem_37_spec (input output : list Z) : Prop :=
  Permutation input output /\
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0) ->
    nth i output 0%Z = nth i input 0%Z) /\
  (forall (i j : nat), i < length output /\ j < length output /\
    i mod 2 = 0 /\ j mod 2 = 0 /\ i < j ->
    (nth i output 0 <= nth j output 0)%Z).

Example problem_37_test :
  problem_37_spec [Z.opp 1%Z; 1%Z; 3%Z; 5%Z] [Z.opp 1%Z; 1%Z; 3%Z; 5%Z].
Proof.
  unfold problem_37_spec.
  split.
  - apply Permutation_refl.
  - split.
    + intros i Hi Hodd.
      simpl. reflexivity.
    + intros i j H.
      destruct H as [Hi [Hj [Hi2 [Hj2 Hij]]]].
      simpl in *.
      destruct i as [| [| [| [| i']]]].
      * (* i = 0 *)
        destruct j as [| [| [| [| j']]]].
        -- (* j = 0, but i < j impossible *)
           lia.
        -- (* j = 1, but j mod 2 = 0 is false *)
           simpl in Hj2; discriminate.
        -- (* j = 2 *)
           simpl. lia.
        -- (* j = 3, but j mod 2 = 0 is false *)
           simpl in Hj2; discriminate.
        -- (* j >= 4, contradicts j < 4 *)
           lia.
      * (* i = 1, but i mod 2 = 0 is false *)
        simpl in Hi2; discriminate.
      * (* i = 2 *)
        destruct j as [| [| [| [| j']]]].
        -- (* j = 0, but i < j impossible *)
           lia.
        -- (* j = 1, but j mod 2 = 0 is false *)
           simpl in Hj2; discriminate.
        -- (* j = 2, but i < j impossible *)
           lia.
        -- (* j = 3, but j mod 2 = 0 is false *)
           simpl in Hj2; discriminate.
        -- (* j >= 4, contradicts j < 4 *)
           lia.
      * (* i = 3, but i mod 2 = 0 is false *)
        simpl in Hi2; discriminate.
      * (* i >= 4, contradicts i < 4 *)
        lia.
Qed.