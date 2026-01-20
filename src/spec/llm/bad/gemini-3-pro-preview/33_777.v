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
  [500; 6; 7; 290; 3; 8; 289; 20; 104; -277; 104; 200; 3; 4; -8; 700; -2; -901; 18; 1000; 7] 
  [-277; 6; 7; 3; 3; 8; 18; 20; 104; 289; 104; 200; 290; 4; -8; 500; -2; -901; 700; 1000; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    vm_compute. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for i = 0 to 20 *)
      do 22 (destruct i; [ try (vm_compute in H; congruence); vm_compute; reflexivity | ]).
      (* For i >= 21, both are None *)
      vm_compute. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        Ltac solve_perm :=
          match goal with
          | |- Permutation [] [] => apply Permutation_refl
          | |- Permutation (?x :: ?l) ?r =>
              let rec find_and_swap pre post :=
                match post with
                | x :: ?tail =>
                    transitivity (x :: pre ++ tail);
                    [ apply Permutation_cons; solve_perm
                    | apply Permutation_sym; apply Permutation_middle ]
                | ?y :: ?tail => find_and_swap (pre ++ [y]) tail
                end
              in find_and_swap (@nil Z) r
          end.
        solve_perm.
      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        repeat (apply Sorted_cons; [ 
          match goal with 
          | |- HdRel _ _ [] => apply HdRel_nil 
          | |- _ => apply HdRel_cons; vm_compute; discriminate 
          end 
        | ]).
        apply Sorted_nil.
Qed.