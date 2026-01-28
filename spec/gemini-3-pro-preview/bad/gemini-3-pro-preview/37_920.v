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
  [5; 3; 10; -8; -5; 2; -9; 0; 123; 1; -10; 10] 
  [-10; 3; -9; -8; -5; 2; 5; 0; 10; 1; 123; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Odd indices *)
      intros i Hlen Hodd.
      do 12 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [5; 10; -5; -9; 123; -10] [-10; -9; -5; 5; 10; 123] *)
        
        apply Permutation_trans with (l' := -10 :: [5; 10; -5; -9; 123]).
        { 
          change [5; 10; -5; -9; 123; -10] with ([5; 10; -5; -9; 123] ++ [-10]).
          apply Permutation_sym.
          apply Permutation_middle.
        }
        apply Permutation_cons.

        apply Permutation_trans with (l' := -9 :: [5; 10; -5; 123]).
        {
          change [5; 10; -5; -9; 123] with ([5; 10; -5] ++ -9 :: [123]).
          apply Permutation_sym.
          apply Permutation_middle.
        }
        apply Permutation_cons.

        apply Permutation_trans with (l' := -5 :: [5; 10; 123]).
        {
          change [5; 10; -5; 123] with ([5; 10] ++ -5 :: [123]).
          apply Permutation_sym.
          apply Permutation_middle.
        }
        apply Permutation_cons.

        apply Permutation_refl.

      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.