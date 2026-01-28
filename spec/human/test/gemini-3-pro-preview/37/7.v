Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* Use Z scope for integer literals *)
Open Scope Z_scope.

(* Pre: no additional constraints for `sort_even` by default *)
Definition problem_37_pre (input : list Z) : Prop := True.

(* Spec definition with explicit scopes to avoid type errors.
   We explicitly use %nat for nat operations like length, mod, < to avoid
   confusion with Z operations in Z_scope. *)
Definition problem_37_spec (input output : list Z) : Prop :=
  (* 1. input is a permutation of output *)
  Permutation input output /\

  (* 2. If index i is odd, output[i] must equal input[i] *)
  (forall (i : nat), (i < length input)%nat -> (i mod 2 <> 0)%nat ->
    nth i output 0 = nth i input 0) /\

  (* 3. Even indices in output must be sorted *)
  (forall (i j : nat), (i < length output)%nat /\ (j < length output)%nat /\
    (i mod 2 = 0)%nat /\ (j mod 2 = 0)%nat /\ (i < j)%nat ->
    nth i output 0 <= nth j output 0).

Example test_case_37: problem_37_spec [11; 7; 6; 9; 14; -1] [6; 7; 11; 9; 14; -1].
Proof.
  unfold problem_37_spec.
  split.
  - (* Goal 1: Permutation *)
    (* Transform [11; 7; 6; 9; 14; -1] to [6; 7; 11; 9; 14; -1] *)
    apply perm_trans with (l' := [11; 6; 7; 9; 14; -1]).
    + apply perm_skip. apply perm_swap.
    + apply perm_trans with (l' := [6; 11; 7; 9; 14; -1]).
      * apply perm_swap.
      * apply perm_skip. apply perm_swap.
  - split.
    + (* Goal 2: Odd indices preservation *)
      intros i Hlen Hodd.
      destruct i. { simpl in Hodd. lia. }
      destruct i. { reflexivity. }
      destruct i. { simpl in Hodd. lia. }
      destruct i. { reflexivity. }
      destruct i. { simpl in Hodd. lia. }
      destruct i. { reflexivity. }
      simpl in Hlen. lia.
    + (* Goal 3: Even indices sorted *)
      intros i j H.
      destruct H as [Hi [Hj [Hie [Hje Hij]]]].
      destruct i.
      * (* i = 0 *)
        destruct j. { lia. }
        destruct j. { simpl in Hje. lia. }
        destruct j. { simpl. lia. } (* 0 vs 2: 6 <= 11 *)
        destruct j. { simpl in Hje. lia. }
        destruct j. { simpl. lia. } (* 0 vs 4: 6 <= 14 *)
        destruct j. { simpl in Hje. lia. }
        simpl in Hj. lia.
      * destruct i. { simpl in Hie. lia. }
        destruct i.
        -- (* i = 2 *)
           destruct j. { lia. }
           destruct j. { lia. }
           destruct j. { lia. }
           destruct j. { simpl in Hje. lia. }
           destruct j. { simpl. lia. } (* 2 vs 4: 11 <= 14 *)
           destruct j. { simpl in Hje. lia. }
           simpl in Hj. lia.
        -- destruct i. { simpl in Hie. lia. }
           destruct i.
           ++ (* i = 4 *)
              destruct j. { lia. }
              destruct j. { lia. }
              destruct j. { lia. }
              destruct j. { lia. }
              destruct j. { lia. }
              destruct j. { simpl in Hje. lia. }
              simpl in Hj. lia.
           ++ destruct i. { simpl in Hie. lia. }
              simpl in Hi. lia.
Qed.