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
  [5; -2; -12; 4; 4; 123; 23; 3; 11; 12; 4; 4] 
  [-12; -2; 4; 4; 4; 123; 5; 3; 11; 12; 23; 4].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 12 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -12; 4; 23; 11; 4] [-12; 4; 4; 5; 11; 23] *)
        apply perm_trans with (l' := 5 :: [-12; 4; 4; 11; 23]).
        { 
          apply perm_skip. (* 5 matches *)
          apply perm_skip. (* -12 matches *)
          apply perm_skip. (* 4 matches *)
          (* Goal: Permutation [23; 11; 4] [4; 11; 23] *)
          apply perm_trans with (l' := 23 :: 4 :: 11 :: []).
          - apply perm_skip. apply perm_swap. (* [11; 4] -> [4; 11] *)
          - apply perm_trans with (l' := 4 :: 23 :: 11 :: []).
            + apply perm_swap. (* [23; 4; 11] -> [4; 23; 11] *)
            + apply perm_skip. apply perm_swap. (* [23; 11] -> [11; 23] *)
        }
        { 
          apply Permutation_sym.
          change ([-12; 4; 4; 5; 11; 23]) with ([-12; 4; 4] ++ 5 :: [11; 23]).
          apply Permutation_middle.
        }
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.