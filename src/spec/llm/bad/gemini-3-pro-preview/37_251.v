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
  [-5; -7; 2; -5; 2; 9; -4; -3; 2; 8; 7; 3; 7; 2; 2] 
  [-5; -7; -4; -5; 2; 9; 2; -3; 2; 8; 2; 3; 7; 2; 7].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Exhaust indices 0 to 14 *)
      do 15 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* Case i >= 15 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current: [-5; 2; 2; -4; 2; 7; 7; 2] *)
        (* Target:  [-5; -4; 2; 2; 2; 2; 7; 7] *)
        apply perm_skip.
        (* Move -4 from index 2 to front *)
        apply Permutation_trans with (l' := -4 :: [2; 2] ++ [2; 7; 7; 2]).
        { apply Permutation_cons_app. }
        simpl. apply perm_skip.
        (* Skip 2, 2, 2 *)
        do 3 apply perm_skip.
        (* Move 2 from index 2 to front *)
        apply Permutation_trans with (l' := 2 :: [7; 7] ++ []).
        { apply Permutation_cons_app. }
        simpl. apply perm_skip.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.