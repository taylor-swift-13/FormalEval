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

Example test_sort_even_case : sort_even_spec [1; 2; 3] [1; 2; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i.
      * (* i = 0 *)
        simpl in Hodd. discriminate Hodd.
      * destruct i.
        -- (* i = 1 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 2 *)
              simpl in Hodd. discriminate Hodd.
           ++ (* i >= 3 *)
              simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl. apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        -- (* Tail is sorted *)
           apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- (* Head relation: 1 <= 3 *)
           apply HdRel_cons.
           lia.
Qed.

Example test_sort_even_case_2 : sort_even_spec 
  [5; 3; -5; 23; -3; 3; -9; 0; 123; 1; 3; -10]
  [-9; 3; -5; 23; -3; 3; 3; 0; 5; 1; 123; -10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [
        try (simpl in Hodd; discriminate Hodd);
        try (simpl; reflexivity)
      | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (5 :: [-9; -5; -3; 3; 123]).
        { apply Permutation_cons.
          apply Permutation_trans with (-5 :: [-9; -3; 3; 123]).
          { apply Permutation_cons.
            apply Permutation_trans with (-3 :: [-9; 3; 123]).
            { apply Permutation_cons.
              apply Permutation_trans with (-9 :: [123; 3]).
              { apply Permutation_cons.
                apply Permutation_swap. }
              { reflexivity. } }
            { replace [-9; -3; 3; 123] with ([-9] ++ -3 :: [3; 123]) by reflexivity.
              apply Permutation_middle. } }
          { replace [-9; -5; -3; 3; 123] with ([-9] ++ -5 :: [-3; 3; 123]) by reflexivity.
            apply Permutation_middle. } }
        { replace [-9; -5; -3; 3; 5; 123] with ([-9; -5; -3; 3] ++ 5 :: [123]) by reflexivity.
          apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.