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

(* Tactics for Permutation proof *)
Ltac find_split x l :=
  match l with
  | x :: ?tl => constr:((@nil Z, tl))
  | ?h :: ?tl =>
      let res := find_split x tl in
      match res with
      | (?a, ?b) => constr:((h :: a, b))
      end
  end.

Ltac solve_perm :=
  simpl;
  repeat match goal with
  | |- Permutation [] [] => apply Permutation_refl
  | |- Permutation (?x :: ?tl) ?r =>
      let pair := find_split x r in
      match pair with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := x :: l1 ++ l2);
          [ apply Permutation_sym; apply Permutation_middle | apply Permutation_cons ]
      end
  end.

(* Tactic for Sorted proof *)
Ltac solve_sorted :=
  simpl;
  repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; cbv; trivial) ]);
  apply Sorted_nil.

Example test_case : sort_third_spec 
  [500; 6; 7; 290; 3; 8; 289; -9; 20; 104; -277; 104; 200; 3; 4; -8; 700; -2; -901; 800; 1000; 7] 
  [-901; 6; 7; -8; 3; 8; 7; -9; 20; 104; -277; 104; 200; 3; 4; 289; 700; -2; 290; 800; 1000; 500].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 23 (destruct i; [ simpl in *; try (case H; reflexivity); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        solve_perm.
      * (* Sorted *)
        solve_sorted.
Qed.