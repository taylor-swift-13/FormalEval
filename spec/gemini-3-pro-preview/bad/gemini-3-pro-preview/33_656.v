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

Ltac find_split x l :=
  match l with
  | x :: ?tl => constr:((@nil Z, tl))
  | ?h :: ?tl =>
      let res := find_split x tl in
      match res with
      | (?l1, ?l2) => constr:((h :: l1, l2))
      end
  end.

Ltac solve_perm_concrete :=
  match goal with
  | [ |- Permutation [] [] ] => apply Permutation_nil
  | [ |- Permutation (?x :: ?xs) ?l ] =>
      let pair := find_split x l in
      match pair with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := x :: (l1 ++ l2));
          [ apply Permutation_cons; solve_perm_concrete
          | apply Permutation_cons_app; reflexivity ]
      end
  end.

Example test_case : sort_third_spec 
  [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901; 3; 3] 
  [-901; 6; 7; -901; 8; 289; 4; -105; -277; 20; 200; 3; 104; 700; 900; 290; 800; 1000; 300; 3; 3].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 21 (destruct i; [
        simpl in H |- *;
        try contradiction;
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl. solve_perm_concrete.
      * simpl.
        repeat (apply Sorted_cons; [ | 
          match goal with
          | [ |- HdRel _ _ [] ] => apply HdRel_nil
          | [ |- HdRel _ _ (_ :: _) ] => apply HdRel_cons; vm_compute; discriminate
          end ]).
        apply Sorted_nil.
Qed.