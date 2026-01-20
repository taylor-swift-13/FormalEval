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
  [5; -4; 3; -5; -3; 3; -12; -2; -9; 0; 123; -2] 
  [-12; -4; -9; -5; -3; 3; 3; -2; 5; 0; 123; -2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ 
        simpl in Hodd; 
        match goal with 
        | H : false = true |- _ => discriminate H 
        | _ => simpl; reflexivity 
        end 
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Move -12 to front *)
        apply Permutation_trans with (l' := -12 :: [5; 3; -3; -9; 123]).
        { change [5; 3; -3; -12; -9; 123] with ([5; 3; -3] ++ -12 :: [-9; 123]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        
        (* Move -9 to front *)
        apply Permutation_trans with (l' := -9 :: [5; 3; -3; 123]).
        { change [5; 3; -3; -9; 123] with ([5; 3; -3] ++ -9 :: [123]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        (* Move -3 to front *)
        apply Permutation_trans with (l' := -3 :: [5; 3; 123]).
        { change [5; 3; -3; 123] with ([5; 3] ++ -3 :: [123]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.

        (* Swap 5 and 3 *)
        apply Permutation_swap.
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