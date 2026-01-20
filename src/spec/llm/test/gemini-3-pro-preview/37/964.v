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

Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply perm_nil
  | |- Permutation (?x :: ?xs) ?ys =>
      let rec find_elem l prefix :=
        match l with
        | x :: ?tl =>
            apply perm_trans with (l' := x :: (prefix ++ tl));
            [ apply perm_skip |
              apply perm_trans with (l' := prefix ++ x :: tl);
              [ apply Permutation_middle | simpl; apply Permutation_refl ] ]
        | ?y :: ?tl => find_elem tl (prefix ++ [y])
        end
      in find_elem ys (@nil Z);
      solve_perm
  end.

Example test_sort_even_case : sort_even_spec [5; -2; -1; -12; 4; 23; 2; 12; 3; 11; 12; -10; 11] [-1; -2; 2; -12; 3; 23; 4; 12; 5; 11; 11; -10; 12].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check for each index 0 to 12 *)
      do 13 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        solve_perm.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; try lia).
Qed.