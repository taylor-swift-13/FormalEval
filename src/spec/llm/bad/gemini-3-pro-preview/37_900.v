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
  | |- Permutation [] [] => apply Permutation_refl
  | |- Permutation (?x :: ?xs) ?ys =>
      let rec find_split pre post :=
        match post with
        | x :: ?post' => 
            apply Permutation_trans with (l' := x :: (pre ++ post'));
            [ apply Permutation_cons; solve_perm
            | apply (Permutation_middle pre post' x) ]
        | ?y :: ?post' => 
            find_split (pre ++ [y]) post'
        end
      in find_split (@nil Z) ys
  end.

Example test_sort_even_case : sort_even_spec 
  [2; 3; 1; 2; 9; 6; 7; 6; 8; 2; 9; 6; 2] 
  [1; 3; 2; 2; 2; 6; 7; 6; 8; 2; 9; 6; 9].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      simpl in Hlen.
      do 13 (destruct i as [|i]; [ 
        try (simpl in Hodd; discriminate); 
        try (simpl; reflexivity) 
      | ]).
      lia.
    + split.
      * cbv [get_evens].
        solve_perm.
      * cbv [get_evens].
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.