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

Ltac solve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?l) ?r =>
      apply Permutation_sym;
      let r' := eval simpl in r in
      match r' with
      | context C [x :: ?t] =>
          let l1 := context C [nil] in
          replace r' with (l1 ++ x :: t) by (simpl; reflexivity);
          apply Permutation_trans with (l' := x :: (l1 ++ t));
          [ | apply Permutation_sym; apply Permutation_middle ];
          apply Permutation_cons;
          apply Permutation_sym;
          simpl;
          solve_perm
      end
  end.

Example test_case : sort_third_spec 
  [300; 500; 7; 290; 8; 289; 20; 104; -277; 900; 8; 6; 200; -8; 700; 900; -901; 800; 1000; 290; -8; 104]
  [20; 500; 7; 104; 8; 289; 200; 104; -277; 290; 8; 6; 300; -8; 700; 900; -901; 800; 900; 290; -8; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 25 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        solve_perm.
      * (* Sorted *)
        simpl.
        repeat (constructor; [ simpl; try lia | ]).
        apply Sorted_nil.
Qed.