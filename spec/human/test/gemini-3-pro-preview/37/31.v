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

Example test_case_37: problem_37_spec [3; 3; 2; 0; 2; 1; 1] [1; 3; 2; 0; 2; 1; 3].
Proof.
  unfold problem_37_spec.
  split.
  - (* Goal 1: Permutation *)
    (* [3; 3; 2; 0; 2; 1; 1] ~ [1; 3; 2; 0; 2; 1; 3] *)
    (* Match first 3 *)
    change [1; 3; 2; 0; 2; 1; 3] with ([1] ++ 3 :: [2; 0; 2; 1; 3]).
    apply Permutation_cons_app. simpl.
    (* [3; 2; 0; 2; 1; 1] ~ [1; 2; 0; 2; 1; 3] *)
    (* Match next 3 (at end) *)
    change [1; 2; 0; 2; 1; 3] with ([1; 2; 0; 2; 1] ++ 3 :: []).
    apply Permutation_cons_app. simpl.
    (* [2; 0; 2; 1; 1] ~ [1; 2; 0; 2; 1] *)
    (* Match 2 (at index 1) *)
    change [1; 2; 0; 2; 1] with ([1] ++ 2 :: [0; 2; 1]).
    apply Permutation_cons_app. simpl.
    (* [0; 2; 1; 1] ~ [1; 0; 2; 1] *)
    (* Match 0 (at index 1) *)
    change [1; 0; 2; 1] with ([1] ++ 0 :: [2; 1]).
    apply Permutation_cons_app. simpl.
    (* [2; 1; 1] ~ [1; 2; 1] *)
    (* Match 2 (at index 1) *)
    change [1; 2; 1] with ([1] ++ 2 :: [1]).
    apply Permutation_cons_app. simpl.
    (* [1; 1] ~ [1; 1] *)
    apply Permutation_refl.
  - split.
    + (* Goal 2: Odd indices preservation *)
      intros i Hlen Hodd.
      destruct i. { simpl in Hodd. lia. } (* 0 *)
      destruct i. { simpl. reflexivity. } (* 1 *)
      destruct i. { simpl in Hodd. lia. } (* 2 *)
      destruct i. { simpl. reflexivity. } (* 3 *)
      destruct i. { simpl in Hodd. lia. } (* 4 *)
      destruct i. { simpl. reflexivity. } (* 5 *)
      destruct i. { simpl in Hodd. lia. } (* 6 *)
      (* i >= 7 *)
      simpl in Hlen. lia.
    + (* Goal 3: Even indices sorted *)
      intros i j H.
      destruct H as [Hi [Hj [Hie [Hje Hij]]]].
      destruct i.
      * (* i = 0 *)
        destruct j; [lia|]. (* 0 *)
        destruct j; [simpl in Hje; lia|]. (* 1 *)
        destruct j; [simpl; lia|]. (* 2: 1 <= 2 *)
        destruct j; [simpl in Hje; lia|]. (* 3 *)
        destruct j; [simpl; lia|]. (* 4: 1 <= 2 *)
        destruct j; [simpl in Hje; lia|]. (* 5 *)
        destruct j; [simpl; lia|]. (* 6: 1 <= 3 *)
        simpl in Hj. lia. (* >= 7 *)
      * destruct i.
        -- (* i = 1 *)
           simpl in Hie. lia.
        -- destruct i.
           ++ (* i = 2 *)
              destruct j; [lia|]. (* 0 *)
              destruct j; [lia|]. (* 1 *)
              destruct j; [lia|]. (* 2 *)
              destruct j; [simpl in Hje; lia|]. (* 3 *)
              destruct j; [simpl; lia|]. (* 4: 2 <= 2 *)
              destruct j; [simpl in Hje; lia|]. (* 5 *)
              destruct j; [simpl; lia|]. (* 6: 2 <= 3 *)
              simpl in Hj. lia. (* >= 7 *)
           ++ destruct i.
              ** (* i = 3 *)
                 simpl in Hie. lia.
              ** destruct i.
                 --- (* i = 4 *)
                     destruct j; [lia|]. (* 0 *)
                     destruct j; [lia|]. (* 1 *)
                     destruct j; [lia|]. (* 2 *)
                     destruct j; [lia|]. (* 3 *)
                     destruct j; [lia|]. (* 4 *)
                     destruct j; [simpl in Hje; lia|]. (* 5 *)
                     destruct j; [simpl; lia|]. (* 6: 2 <= 3 *)
                     simpl in Hj. lia. (* >= 7 *)
                 --- destruct i.
                     +++ (* i = 5 *)
                         simpl in Hie. lia.
                     +++ destruct i.
                         *** (* i = 6 *)
                             destruct j; [lia|]. (* 0 *)
                             destruct j; [lia|]. (* 1 *)
                             destruct j; [lia|]. (* 2 *)
                             destruct j; [lia|]. (* 3 *)
                             destruct j; [lia|]. (* 4 *)
                             destruct j; [lia|]. (* 5 *)
                             destruct j; [lia|]. (* 6 *)
                             simpl in Hj. lia. (* >= 7 *)
                         *** (* i >= 7 *)
                             simpl in Hi. lia.
Qed.