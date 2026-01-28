Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [1; 5; 2; 7; 9; 3; -7; 11; 0; 1; 13; 6; -2; 8; 19] 
  [-7; 5; 2; -2; 9; 3; 1; 11; 0; 1; 13; 6; 7; 8; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Handle indices 0 to 14 explicitly *)
      do 15 (destruct i as [|i]; [
        simpl in *; 
        try contradiction; (* Solving cases where i mod 3 = 0 *)
        reflexivity        (* Solving cases where i mod 3 <> 0 *)
      | ]).
      (* For i >= 15, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: [-7; -2; 1; 1; 7] ~p [1; 7; -7; 1; -2] *)
        apply Permutation_sym.
        (* Goal: [1; 7; -7; 1; -2] ~p [-7; -2; 1; 1; 7] *)
        
        (* Move -7 to front *)
        assert (H1: Permutation [1; 7; -7; 1; -2] (-7 :: [1; 7; 1; -2])).
        { change [1; 7; -7; 1; -2] with ([1; 7] ++ -7 :: [1; -2]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (l' := -7 :: [1; 7; 1; -2]); [exact H1 | ].
        apply Permutation_cons.
        
        (* Move -2 to front *)
        assert (H2: Permutation [1; 7; 1; -2] (-2 :: [1; 7; 1])).
        { change [1; 7; 1; -2] with ([1; 7; 1] ++ -2 :: []).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (l' := -2 :: [1; 7; 1]); [exact H2 | ].
        apply Permutation_cons.
        
        (* Match 1 *)
        apply Permutation_cons.
        
        (* Match 1 and 7 *)
        apply Permutation_swap.

      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [-7; -2; 1; 1; 7] *)
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; simpl; lia.
        -- apply HdRel_cons; simpl; lia.
        -- apply HdRel_cons; simpl; lia.
        -- apply HdRel_cons; simpl; lia.
Qed.