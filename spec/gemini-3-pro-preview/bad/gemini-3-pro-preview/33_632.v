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

Example test_case : sort_third_spec 
  [500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; 104]
  [-901; 6; 7; 4; 8; 289; 20; -105; -277; 104; 200; 3; 104; 700; 900; 290; 800; 1000; 500].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 19 (destruct i; [ vm_compute in H; try congruence; vm_compute; reflexivity | ]).
      vm_compute. reflexivity.
    + split.
      * cbv [extract_thirds].
        let rec solve_add :=
          match goal with
          | |- Add ?x ?l (?x :: ?l) => apply Add_head
          | |- Add ?x ?l (?y :: ?l') => apply Add_cons; solve_add
          end in
        let rec solve_perm :=
          match goal with
          | |- Permutation [] [] => apply Permutation_nil
          | |- Permutation (?a :: ?l) ?l' =>
              eapply Permutation_Add_cons; [ solve_add | solve_perm ]
          end in
        solve_perm.
      * cbv [extract_thirds].
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.