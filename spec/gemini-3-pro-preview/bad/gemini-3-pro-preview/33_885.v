Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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

Ltac find_split x l :=
  match l with
  | ?h :: ?tl =>
      match x with
      | h => constr:((@nil Z, tl))
      | _ =>
          let res := find_split x tl in
          match res with
          | (?l1, ?l2) => constr:((h :: l1, l2))
          end
      end
  end.

Ltac solve_perm :=
  simpl;
  repeat match goal with
  | |- Permutation [] [] => apply perm_nil
  | |- Permutation (?x :: ?xs) ?ys =>
      let res := find_split x ys in
      match res with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := x :: (l1 ++ l2));
          [ apply perm_skip | apply Permutation_sym; apply Permutation_middle ]
      end
  end.

Example test_case : sort_third_spec 
  [300; 6; 7; 290; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; 700; -901; 800; -901; 20; 3; 6; 8; 8] 
  [-901; 6; 7; -105; 289; 20; 8; -277; 104; 20; 3; 4; 200; 900; 700; 290; 800; -901; 300; 3; 6; 700; 8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try (exfalso; lia); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.