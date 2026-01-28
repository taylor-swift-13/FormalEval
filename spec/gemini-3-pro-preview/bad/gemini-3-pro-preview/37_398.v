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

Example test_sort_even_case : sort_even_spec [5; 3; -5; 2; -3; -2; -9; 0; 123; 1; -10; -9; -10] [-10; 3; -10; 2; -9; -2; -5; 0; -3; 1; 5; -9; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i as [|i]; [
        try (simpl in Hodd; discriminate);
        try (simpl; reflexivity)
      | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        transitivity (5 :: ([-10; -10; -9; -5; -3] ++ [123])).
        { apply Permutation_cons.
          transitivity (-5 :: ([-10; -10; -9] ++ [-3; 123])).
          { apply Permutation_cons.
            transitivity (-3 :: ([-10; -10; -9] ++ [123])).
            { apply Permutation_cons.
              transitivity (-9 :: ([-10; -10] ++ [123])).
              { apply Permutation_cons.
                transitivity (123 :: ([-10; -10] ++ [])).
                { apply Permutation_cons.
                  simpl. apply Permutation_refl. }
                { apply Permutation_sym. apply (Permutation_middle [-10; -10] [] 123). }
              }
              { apply Permutation_sym. apply (Permutation_middle [-10; -10] [123] (-9)). }
            }
            { apply Permutation_sym. apply (Permutation_middle [-10; -10; -9] [123] (-3)). }
          }
          { apply Permutation_sym. apply (Permutation_middle [-10; -10; -9] [-3; 123] (-5)). }
        }
        { apply Permutation_sym. apply (Permutation_middle [-10; -10; -9; -5; -3] [123] 5). }
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
        apply HdRel_nil.
Qed.