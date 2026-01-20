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

(* Helper function to split a list around the first occurrence of x *)
Fixpoint split_pivot (x : Z) (l : list Z) : (list Z * list Z) :=
  match l with
  | [] => ([], [])
  | y :: tl => if (x =? y) then ([], tl)
               else let (l1, l2) := split_pivot x tl in (y :: l1, l2)
  end.

(* Tactic to solve Permutation goals for concrete lists *)
Ltac solve_perm :=
  simpl;
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?xs) ?ys =>
      let res := eval compute in (split_pivot x ys) in
      match res with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := x :: l1 ++ l2);
          [ apply Permutation_cons; solve_perm
          | change ys with (l1 ++ x :: l2); apply Permutation_middle ]
      end
  end.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 9; 104; 200; 3; 4; 5; 700; 900; -200; -104; -901; 800; 6; 1000]
  [-104; 500; 6; 3; 8; 289; 6; -105; -277; 7; 104; 200; 9; 4; 5; 20; 900; -200; 300; -901; 800; 700; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i enough times to cover the list length (23 elements) *)
      do 23 (destruct i as [|i]; [ 
        try (exfalso; apply H; reflexivity); (* Case i mod 3 = 0 *)
        try reflexivity (* Case i mod 3 <> 0 *) 
      | ]).
      (* For i >= 23, both lists are out of bounds (None) *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        solve_perm.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_nil || (apply HdRel_cons; vm_compute; intro H; discriminate) | ]).
        apply Sorted_nil.
Qed.