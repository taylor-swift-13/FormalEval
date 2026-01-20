Existing Coq output file content 
specification for the first test case `input = [[1%Z; 2%Z; 3%Z]], output = [1%Z; 2%Z; 3%Z]`:
```coq
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

(* Tactic to prove Permutation of concrete lists by peeling elements *)
Ltac peel_perm :=
  match goal with
  | [ |- Permutation [] [] ] => apply Permutation_nil
  | [ |- Permutation (?x :: ?xs) ?ys ] =>
      let ys_red := eval vm_compute in ys in
      change ys with ys_red;
      let rec find l1 l2 :=
        match l2 with
        | ?y :: ?rest =>
            tryif constr_eq x y then (
                let new_ys := constr:(l1 ++ x :: rest) in
                change ys_red with new_ys;
                apply Permutation_trans with (l' := x :: (l1 ++ rest));
                [ apply Permutation_cons; peel_perm
                | apply Permutation_middle ]
            ) else (
                find (l1 ++ [y]) rest
            )
        | [] => fail 1 "Element not found in permutation"
        end
      in find (@nil Z) ys_red
  end.

Example test_case : sort_third_spec 
  [29; 9; 8; 7; 6; 5; 4; 2; 0; -6; -1; -3; -4; 800; -5; -7; -8; -9; -11; -2; -1; -6]
  [-11; 9; 8; -7; 6; 5; -6; 2; 0; -6; -1; -3; -4; 800; -5; 4; -8; -9; 7; -2; -1; 29].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    reflexivity.
  - split.
    + (* Indices preservation *)
      intros i H.
      (* The list has length 22. We check i from 0 to 21. *)
      do 22 (destruct i as [|i]; [
        (* For each index, check if mod 3 <> 0 *)
        vm_compute in H; (* Reduces condition *)
        try (exfalso; apply H; reflexivity); (* If mod 3 = 0, H is False *)
        vm_compute; reflexivity (* If mod 3 <> 0, check equality *)
      | ]).
      (* i >= 22 *)
      vm_compute. reflexivity.
    + split.
      * (* Permutation *)
        match goal with
        | [ |- Permutation ?L ?R ] =>
          let L' := eval vm_compute in L in
          let R' := eval vm_compute in R in
          change (Permutation L' R')
        end.
        peel_perm.
      * (* Sorted *)
        match goal with
        | [ |- Sorted ?R ?L ] =>
          let L' := eval vm_compute in L in
          change (Sorted R L')
        end.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; [ reflexivity | ] || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.