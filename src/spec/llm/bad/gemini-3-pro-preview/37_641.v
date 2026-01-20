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

Example test_sort_even_case : sort_even_spec [5; 3; -5; 2; -2; 3; -9; 0; 123; 1; -10; 1] [-10; 3; -9; 2; -5; 3; -2; 0; 5; 1; 123; 1].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | idtac ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply Permutation_trans with (l' := 5 :: [-10; -9; -5; -2; 123]).
        { apply Permutation_cons.
          apply Permutation_trans with (l' := -5 :: [-10; -9; -2; 123]).
          { apply Permutation_cons.
            apply Permutation_trans with (l' := -2 :: [-10; -9; 123]).
            { apply Permutation_cons.
              apply Permutation_trans with (l' := -9 :: [-10; 123]).
              { apply Permutation_cons.
                change ([-10; 123]) with ([-10] ++ 123 :: []).
                apply Permutation_middle. }
              { change ([-10; -9; 123]) with ([-10] ++ -9 :: [123]).
                apply Permutation_middle. }
            }
            { change ([-10; -9; -2; 123]) with ([-10; -9] ++ -2 :: [123]).
              apply Permutation_middle. }
          }
          { change ([-10; -9; -5; -2; 123]) with ([-10; -9] ++ -5 :: [-2; 123]).
            apply Permutation_middle. }
        }
        { change ([-10; -9; -5; -2; 5; 123]) with ([-10; -9; -5; -2] ++ 5 :: [123]).
          apply Permutation_middle. }
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | idtac ]).
        apply Sorted_nil.
Qed.