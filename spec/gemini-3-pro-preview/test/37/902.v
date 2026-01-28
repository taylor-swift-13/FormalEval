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
  [5; 3; 10; -5; 2; -12; -3; 3; -9; 1; 123; -10; 10; -5] 
  [-9; 3; -3; -5; 2; -12; 5; 3; 10; 1; 10; -10; 123; -5].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 14 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * simpl.
        transitivity (5 :: [-9; -3; 2] ++ [10; 10; 123]).
        { apply perm_skip. simpl.
          transitivity (10 :: [-9; -3; 2] ++ [10; 123]).
          { apply perm_skip. simpl.
            transitivity (2 :: [-9; -3] ++ [10; 123]).
            { apply perm_skip. simpl.
              transitivity (-3 :: [-9] ++ [10; 123]).
              { apply perm_skip. simpl.
                apply perm_skip.
                transitivity (123 :: [10] ++ []).
                { apply perm_skip. simpl. apply perm_skip. apply perm_nil. }
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
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.