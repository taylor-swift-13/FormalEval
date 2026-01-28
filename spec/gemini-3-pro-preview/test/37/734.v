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
  [5; -2; -1; -12; 4; 23; 2; 3; 11; 12; -10] 
  [-10; -2; -1; -12; 2; 23; 4; 3; 5; 12; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 11 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* We prove Permutation l_sorted l_original by swapping elements *)
        apply Permutation_sym.
        
        (* Move -10 *)
        apply Permutation_trans with (l' := -10 :: ([5; -1; 4; 2; 11] ++ [])).
        2: apply Permutation_middle.
        constructor. simpl.
        
        (* Move -1 *)
        apply Permutation_trans with (l' := -1 :: ([5] ++ [4; 2; 11])).
        2: apply Permutation_middle.
        constructor. simpl.
        
        (* Move 2 *)
        apply Permutation_trans with (l' := 2 :: ([5; 4] ++ [11])).
        2: apply Permutation_middle.
        constructor. simpl.
        
        (* Move 4 *)
        apply Permutation_trans with (l' := 4 :: ([5] ++ [11])).
        2: apply Permutation_middle.
        constructor. simpl.
        
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.