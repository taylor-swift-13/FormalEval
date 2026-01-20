Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec [5; -2; -12; 4; 23; 2; 3; 3; 11; 12; -10; 3] [-12; -2; -10; 4; 3; 2; 5; 3; 11; 12; 23; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -12; 23; 3; 11; -10] [-12; -10; 3; 5; 11; 23] *)
        
        (* 3.1 Move -12 to front *)
        transitivity (-12 :: [5; 23; 3; 11; -10]).
        { change [5; -12; 23; 3; 11; -10] with ([5] ++ -12 :: [23; 3; 11; -10]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        (* 3.2 Move -10 to front *)
        transitivity (-10 :: [5; 23; 3; 11]).
        { change [5; 23; 3; 11; -10] with ([5; 23; 3; 11] ++ -10 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        (* 3.3 Move 3 to front *)
        transitivity (3 :: [5; 23; 11]).
        { change [5; 23; 3; 11] with ([5; 23] ++ 3 :: [11]).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        (* 3.4 5 is already at front *)
        apply Permutation_cons.
        
        (* 3.5 Move 11 to front *)
        transitivity (11 :: [23]).
        { change [23; 11] with ([23] ++ 11 :: []).
          apply Permutation_sym, Permutation_middle. }
        apply Permutation_cons.
        
        (* 3.6 Last element *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.