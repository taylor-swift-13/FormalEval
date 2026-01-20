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

Example test_sort_even_case : sort_even_spec 
  [5; 3; -5; -3; -9; 0; 123; 1; -10; 123; 123] 
  [-10; 3; -9; -3; -5; 0; 5; 1; 123; 123; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check indices 0 to 10. Odd indices (1, 3, 5, 7, 9) must match. *)
      do 12 (destruct i as [|i]; [ 
        simpl in Hodd; try discriminate Hodd; simpl; reflexivity 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -5; -9; 123; -10; 123] [-10; -9; -5; 5; 123; 123] *)
        
        (* Move -10 to front *)
        apply Permutation_trans with (l' := -10 :: [5; -5; -9; 123; 123]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        (* Move -9 to front *)
        apply Permutation_trans with (l' := -9 :: [5; -5; 123; 123]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        (* Move -5 to front *)
        apply Permutation_trans with (l' := -5 :: [5; 123; 123]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        
        (* Remaining list [5; 123; 123] matches *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.