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
  [11; -7; 2; 10; 0; 5; -3; 2; 8; 3; 7; 5] 
  [-3; -7; 0; 10; 2; 5; 7; 2; 8; 3; 11; 5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := 11 :: [-3; 0; 2; 7; 8] ++ []).
        { apply Permutation_cons.
          apply Permutation_trans with (l' := 2 :: [-3; 0] ++ [7; 8]).
          { apply Permutation_cons.
            apply Permutation_trans with (l' := 0 :: [-3] ++ [7; 8]).
            { apply Permutation_cons.
              apply Permutation_trans with (l' := -3 :: [] ++ [7; 8]).
              { apply Permutation_cons.
                apply Permutation_trans with (l' := 8 :: [7] ++ []).
                { apply Permutation_cons. apply Permutation_refl. }
                { apply Permutation_middle. }
              }
              { apply Permutation_middle. }
            }
            { apply Permutation_middle. }
          }
          { apply Permutation_middle. }
        }
        { apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.