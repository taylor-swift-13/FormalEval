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
  [2; 2; 3; 4; 6; 7; 7; 8; 2; 2; 7; 6; 6] 
  [2; 2; 2; 4; 3; 7; 6; 8; 6; 2; 7; 6; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check each index i from 0 to 12 explicitly to avoid large proof terms or timeouts *)
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* For i >= 13, contradict length hypothesis *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [2; 3; 6; 7; 2; 7; 6] [2; 2; 3; 6; 6; 7; 7] *)
        apply perm_skip.
        (* Goal: Permutation [3; 6; 7; 2; 7; 6] [2; 3; 6; 6; 7; 7] *)
        (* Move 2 from middle to front in LHS using Permutation_middle symmetry *)
        apply Permutation_trans with (2 :: [3; 6; 7] ++ [7; 6]).
        { apply Permutation_sym, Permutation_middle. }
        simpl. apply perm_skip.
        (* Goal: Permutation [3; 6; 7; 7; 6] [3; 6; 6; 7; 7] *)
        apply perm_skip.
        (* Goal: Permutation [6; 7; 7; 6] [6; 6; 7; 7] *)
        apply perm_skip.
        (* Goal: Permutation [7; 7; 6] [6; 7; 7] *)
        (* Move 6 from end to front *)
        apply Permutation_trans with (6 :: [7; 7] ++ []).
        { apply Permutation_sym, Permutation_middle. }
        simpl. apply perm_skip.
        (* Goal: Permutation [7; 7] [7; 7] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.