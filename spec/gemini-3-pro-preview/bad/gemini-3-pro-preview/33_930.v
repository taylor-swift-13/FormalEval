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

Definition input_l := [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 289; 3; 4; 700; 8; 300; 900; -901; 800; 1000; -901; 1000].
Definition output_res := [-901; 6; 7; -901; 8; 289; 3; -105; -277; 8; 200; 289; 20; 4; 700; 104; 300; 900; 290; 800; 1000; 300; 1000].

Example test_case : sort_third_spec input_l output_res.
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check indices 0 to 22 *)
      do 23 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      (* Indices >= 23 *)
      simpl. reflexivity.
    + split.
      * simpl. apply Permutation_sym.
        (* We prove Permutation sorted unsorted *)
        (* Sorted: [-901; -901; 3; 8; 20; 104; 290; 300] *)
        (* Unsorted: [300; 290; 20; 104; 3; 8; -901; -901] *)
        
        apply (Permutation_cons_app _ [300; 290; 20; 104; 3; 8] [-901]). simpl.
        apply (Permutation_cons_app _ [300; 290; 20; 104; 3; 8] []). simpl.
        apply (Permutation_cons_app _ [300; 290; 20; 104] [8]). simpl.
        apply (Permutation_cons_app _ [300; 290; 20; 104] []). simpl.
        apply (Permutation_cons_app _ [300; 290] [104]). simpl.
        apply (Permutation_cons_app _ [300; 290] []). simpl.
        apply (Permutation_cons_app _ [300] []). simpl.
        apply (Permutation_cons_app _ [] []). simpl.
        apply Permutation_nil.
      * simpl.
        repeat (apply Sorted_cons; [
          simpl; try apply HdRel_nil; try (apply HdRel_cons; simpl; lia)
        | ]).
        apply Sorted_nil.
Qed.