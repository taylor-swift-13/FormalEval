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
  [6; 3; 6; 1; 4; 1; 10; 9; 2; 6; 2; 5; 3; 6] 
  [2; 3; 2; 1; 3; 1; 4; 9; 6; 6; 6; 5; 10; 6].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply Permutation_sym.
        
        (* Move 2 *)
        assert (H1: [6; 6; 4; 10; 2; 2; 3] = [6; 6; 4; 10] ++ 2 :: [2; 3]) by reflexivity.
        rewrite H1; clear H1.
        apply Permutation_trans with (l' := 2 :: ([6; 6; 4; 10] ++ [2; 3])).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.

        (* Move 2 *)
        assert (H2: [6; 6; 4; 10; 2; 3] = [6; 6; 4; 10] ++ 2 :: [3]) by reflexivity.
        rewrite H2; clear H2.
        apply Permutation_trans with (l' := 2 :: ([6; 6; 4; 10] ++ [3])).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.

        (* Move 3 *)
        assert (H3: [6; 6; 4; 10; 3] = [6; 6; 4; 10] ++ 3 :: []) by reflexivity.
        rewrite H3; clear H3.
        apply Permutation_trans with (l' := 3 :: ([6; 6; 4; 10] ++ [])).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.

        (* Move 4 *)
        assert (H4: [6; 6; 4; 10] = [6; 6] ++ 4 :: [10]) by reflexivity.
        rewrite H4; clear H4.
        apply Permutation_trans with (l' := 4 :: ([6; 6] ++ [10])).
        2: { apply Permutation_sym. apply Permutation_middle. }
        apply perm_skip.
        simpl.

        (* Remaining matches *)
        apply Permutation_refl.

      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.