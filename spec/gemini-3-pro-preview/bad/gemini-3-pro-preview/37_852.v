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

Example test_sort_even_case : sort_even_spec [1; 1; 1; 2; -12; 0; 1; 9; 1; -5; -5] [-12; 1; -5; 2; 1; 0; 1; 9; 1; -5; 1].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [1; 1; -12; 1; 1; -5] [-12; -5; 1; 1; 1; 1] *)
        transitivity (-12 :: [1; 1; 1; 1; -5]).
        { 
          change [1; 1; -12; 1; 1; -5] with ([1; 1] ++ -12 :: [1; 1; -5]).
          apply Permutation_sym. 
          apply Permutation_middle. 
        }
        apply perm_skip.
        (* Goal: Permutation [1; 1; 1; 1; -5] [-5; 1; 1; 1; 1] *)
        transitivity (-5 :: [1; 1; 1; 1]).
        {
          change [1; 1; 1; 1; -5] with ([1; 1; 1; 1] ++ -5 :: []).
          apply Permutation_sym.
          apply Permutation_middle.
        }
        apply perm_skip.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.