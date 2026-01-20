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

Example test_sort_even_case : sort_even_spec [5; 3; -5; 2; -3; 3; -9; 0; 6; 123; 1; -10; 123] [-9; 3; -5; 2; -3; 3; 1; 0; 5; 123; 6; -10; 123].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We handle indices 0 to 12. *)
      do 13 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      (* Remaining case i >= 13 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [5; -5; -3; -9; 6; 1; 123] [-9; -5; -3; 1; 5; 6; 123] *)
        apply Permutation_trans with (l' := -9 :: [5; -5; -3; 6; 1; 123]).
        { apply Permutation_sym.
          change [5; -5; -3; -9; 6; 1; 123] with ([5; -5; -3] ++ -9 :: [6; 1; 123]).
          apply Permutation_cons_app. apply Permutation_refl. }
        apply Permutation_cons.
        (* Goal: Permutation [5; -5; -3; 6; 1; 123] [-5; -3; 1; 5; 6; 123] *)
        apply Permutation_trans with (l' := -5 :: [5; -3; 6; 1; 123]).
        { apply Permutation_sym.
          change [5; -5; -3; 6; 1; 123] with ([5] ++ -5 :: [-3; 6; 1; 123]).
          apply Permutation_cons_app. apply Permutation_refl. }
        apply Permutation_cons.
        (* Goal: Permutation [5; -3; 6; 1; 123] [-3; 1; 5; 6; 123] *)
        apply Permutation_trans with (l' := -3 :: [5; 6; 1; 123]).
        { apply Permutation_sym.
          change [5; -3; 6; 1; 123] with ([5] ++ -3 :: [6; 1; 123]).
          apply Permutation_cons_app. apply Permutation_refl. }
        apply Permutation_cons.
        (* Goal: Permutation [5; 6; 1; 123] [1; 5; 6; 123] *)
        apply Permutation_trans with (l' := 1 :: [5; 6; 123]).
        { apply Permutation_sym.
          change [5; 6; 1; 123] with ([5; 6] ++ 1 :: [123]).
          apply Permutation_cons_app. apply Permutation_refl. }
        apply Permutation_cons.
        (* Goal: Permutation [5; 6; 123] [5; 6; 123] *)
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; lia]).
        apply Sorted_nil.
Qed.