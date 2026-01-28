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
  [300; 6; 7; 290; -276; 289; 20; -105; -277; 104; 200; 3; -8; 4; -9; 700; 900; -901; 800; 1000; -901; 104; 899; 17; 3; 7]
  [-8; 6; 7; 3; -276; 289; 20; -105; -277; 104; 200; 3; 104; 4; -9; 290; 900; -901; 300; 1000; -901; 700; 899; 17; 800; 7].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices preservation *)
      intros i H.
      (* We check indices 0 to 25. The 27th case handles i >= 26 *)
      do 27 (destruct i; [ simpl in *; try (compute in H; congruence); try reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* permutation *)
        simpl.
        (* Tactic to solve Permutation for concrete lists by stripping elements one by one *)
        repeat (match goal with 
                | |- Permutation (?x :: ?xs) ?ys => 
                    eapply Permutation_trans; 
                    [ | apply Permutation_Add; repeat constructor ]; 
                    apply Permutation_cons 
                end).
        apply Permutation_refl.
      * (* sorted *)
        simpl.
        repeat (apply Sorted_cons; 
                [ try apply HdRel_nil; try (apply HdRel_cons; vm_compute; try discriminate) 
                | ]).
        apply Sorted_nil.
Qed.