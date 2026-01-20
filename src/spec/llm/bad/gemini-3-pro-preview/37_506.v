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
  [-5; -7; 2; -5; 2; 9; 5; -3; 2; 8; 7; 3; 7; 12; 2; 11; 9; 8] 
  [-5; -7; 2; -5; 2; 9; 2; -3; 2; 8; 5; 3; 7; 12; 7; 11; 9; 8].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 18 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current LHS: [-5; 2; 2; 5; 2; 7; 7; 2; 9] *)
        (* Current RHS: [-5; 2; 2; 2; 2; 5; 7; 7; 9] *)
        apply perm_skip. apply perm_skip. apply perm_skip.
        (* Goal: Permutation [5; 2; 7; 7; 2; 9] [2; 2; 5; 7; 7; 9] *)
        apply Permutation_trans with (l' := 5 :: [2; 2] ++ [7; 7; 9]).
        { apply Permutation_cons. 
          (* Goal: Permutation [2; 7; 7; 2; 9] ([2; 2] ++ [7; 7; 9]) *)
          simpl. apply perm_skip.
          (* Goal: Permutation [7; 7; 2; 9] [2; 7; 7; 9] *)
          apply Permutation_trans with (l' := 7 :: [2] ++ [7; 9]).
          { apply Permutation_cons.
            (* Goal: Permutation [7; 2; 9] ([2] ++ [7; 9]) *)
            simpl. apply Permutation_trans with (l' := 7 :: [2] ++ [9]).
            { apply Permutation_cons.
              (* Goal: Permutation [2; 9] ([2] ++ [9]) *)
              simpl. apply Permutation_refl.
            }
            { apply Permutation_middle. }
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; lia]).
        apply Sorted_nil.
Qed.