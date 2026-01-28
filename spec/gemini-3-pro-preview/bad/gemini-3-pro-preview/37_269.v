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
  [-5; -7; 2; -5; 2; 9; 5; -4; -12; 2; 8; 7; 3; 7; 2; 2] 
  [-12; -7; -5; -5; 2; 9; 2; -4; 2; 2; 3; 7; 5; 7; 8; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 17 (destruct i as [|i]; [
        simpl in *;
        try discriminate Hodd;
        try reflexivity
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS evens: [-5; 2; 2; 5; -12; 8; 3; 2] *)
        (* RHS evens: [-12; -5; 2; 2; 2; 3; 5; 8] *)
        
        (* Move -5 to front *)
        apply Permutation_trans with (l' := -5 :: [-12; 2; 2; 2; 3; 5; 8]).
        { apply Permutation_cons.
          (* Move 2 to front *)
          apply Permutation_trans with (l' := 2 :: [-12; 2; 2; 3; 5; 8]).
          { apply Permutation_cons.
            (* Move 2 to front *)
            apply Permutation_trans with (l' := 2 :: [-12; 2; 3; 5; 8]).
            { apply Permutation_cons.
              (* Move 5 to front *)
              apply Permutation_trans with (l' := 5 :: [-12; 2; 3; 8]).
              { apply Permutation_cons.
                (* Move -12 to front *)
                apply Permutation_trans with (l' := -12 :: [2; 3; 8]).
                { apply Permutation_cons.
                  (* Move 8 to front *)
                  apply Permutation_trans with (l' := 8 :: [2; 3]).
                  { apply Permutation_cons.
                    (* Move 3 to front *)
                    apply Permutation_trans with (l' := 3 :: [2]).
                    { apply Permutation_cons.
                      (* Last element 2 matches *)
                      apply Permutation_refl. }
                    { apply Permutation_sym. apply Permutation_middle with (l1 := [2]). } }
                  { apply Permutation_sym. apply Permutation_middle with (l1 := [2; 3]). } }
                { apply Permutation_refl. } }
              { apply Permutation_sym. apply Permutation_middle with (l1 := [-12; 2; 3]). } }
            { apply Permutation_sym. apply Permutation_middle with (l1 := [-12]). } }
          { apply Permutation_sym. apply Permutation_middle with (l1 := [-12]). } }
        { apply Permutation_sym. apply Permutation_middle with (l1 := [-12]). }
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.