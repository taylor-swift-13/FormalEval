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
  [122; 5; 3; -5; 2; -3; -9; 0; 123; 1; -10; 123] 
  [-10; 5; -9; -5; 2; -3; 3; 0; 122; 1; 123; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Handle indices 0 to 11 explicitly *)
      repeat (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      (* For i >= 12 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [122; 3; 2; -9; 123; -10] [-10; -9; 2; 3; 122; 123] *)
        
        (* Strategy: Move matching elements to the front using Permutation_middle *)
        
        (* Move -10 *)
        change [122; 3; 2; -9; 123; -10] with ([122; 3; 2; -9; 123] ++ [-10]).
        apply Permutation_trans with (l' := -10 :: [122; 3; 2; -9; 123]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move -9 *)
        change [122; 3; 2; -9; 123] with ([122; 3; 2] ++ -9 :: [123]).
        apply Permutation_trans with (l' := -9 :: [122; 3; 2; 123]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 2 *)
        change [122; 3; 2; 123] with ([122; 3] ++ 2 :: [123]).
        apply Permutation_trans with (l' := 2 :: [122; 3; 123]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move 3 *)
        change [122; 3; 123] with ([122] ++ 3 :: [123]).
        apply Permutation_trans with (l' := 3 :: [122; 123]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Remaining list [122; 123] matches *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- repeat (apply HdRel_cons; lia).
Qed.