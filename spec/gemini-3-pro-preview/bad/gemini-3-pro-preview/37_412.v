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
  [2; 3; 4; 5; 7; -4; 9; 2; 5; 4] 
  [2; 3; 4; 5; 5; -4; 7; 2; 9; 4].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check indices 0 to 9 *)
      do 10 (destruct i; [ simpl in Hodd; try discriminate; simpl; try reflexivity | ]).
      (* For i >= 10 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [2; 4; 7; 9; 5] [2; 4; 5; 7; 9] *)
        apply perm_skip. (* Matches 2 *)
        apply perm_skip. (* Matches 4 *)
        (* Goal: Permutation [7; 9; 5] [5; 7; 9] *)
        apply perm_trans with (l' := [7; 5; 9]).
        -- (* [7; 9; 5] -> [7; 5; 9] *)
           apply perm_skip. apply perm_swap.
        -- (* [7; 5; 9] -> [5; 7; 9] *)
           apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try lia]).
        apply Sorted_nil.
Qed.