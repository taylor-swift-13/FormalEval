Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Ltac solve_perm_step :=
  match goal with
  | |- Permutation ?L (?x :: ?R) =>
      let rec find_split l acc :=
        match l with
        | ?h :: ?tl =>
            tryif constr_eq h x 
            then constr:((acc, tl))
            else find_split tl (acc ++ [h])
        end
      in
      let parts := find_split L (@nil Z) in
      match parts with
      | (?l1, ?l2) =>
         transitivity (x :: (l1 ++ l2));
         [ apply Permutation_sym;
           change L with (l1 ++ x :: l2);
           apply Permutation_Add;
           apply Add_app
         | apply Permutation_cons ]
      end
  | |- Permutation [] [] => apply Permutation_nil
  end.

Ltac solve_perm := repeat solve_perm_step.

Example test_case : sort_third_spec 
  [500; 6; 7; (-2); 8; 289; 20; (-105); (-277); 104; 200; 3; 4; 5; 11; 700; (-200); (-901); 800; 1000; (-277); 289; (-105)]
  [(-2); 6; 7; 4; 8; 289; 20; (-105); (-277); 104; 200; 3; 289; 5; 11; 500; (-200); (-901); 700; 1000; (-277); 800; (-105)].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i as [|i]; [ 
        simpl; try (exfalso; apply H; reflexivity); try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl. solve_perm.
      * simpl. repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; vm_compute; reflexivity) ]).
        apply Sorted_nil.
Qed.