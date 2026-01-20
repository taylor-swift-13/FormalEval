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
  [-4; 7; 9; -6; 3; 11; -8; 6; 2; -11; 1; 8; 14; 0; 4; 6; 9; 2; 0] 
  [-11; 7; 9; -8; 3; 11; -6; 6; 2; -4; 1; 8; 0; 0; 4; 6; 9; 2; 14].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Handle indices 0 to 18 explicitly *)
      do 19 (destruct i as [|i]; [ 
        simpl in *; 
        try (exfalso; apply H; reflexivity); (* Case i%3 == 0: H is False *)
        try reflexivity                      (* Case i%3 != 0: check nth_error *)
      | ]).
      (* Handle i >= 19 *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation for concrete lists by moving elements to head *)
        (* Target: [-11; -8; -6; -4; 0; 6; 14] *)
        (* Source: [-4; -6; -8; -11; 14; 6; 0] *)
        
        (* 1. Match -11 *)
        change [-4; -6; -8; -11; 14; 6; 0] with ([-4; -6; -8] ++ -11 :: [14; 6; 0]).
        apply Permutation_cons_app.
        
        (* 2. Match -8 *)
        change ([-4; -6; -8] ++ [14; 6; 0]) with ([-4; -6] ++ -8 :: [14; 6; 0]).
        apply Permutation_cons_app.
        
        (* 3. Match -6 *)
        change ([-4; -6] ++ [14; 6; 0]) with ([-4] ++ -6 :: [14; 6; 0]).
        apply Permutation_cons_app.
        
        (* 4. Match -4 (at head) *)
        apply Permutation_cons.
        
        (* 5. Match 0 *)
        change [14; 6; 0] with ([14; 6] ++ 0 :: []).
        apply Permutation_cons_app.
        
        (* 6. Match 6 *)
        change ([14; 6] ++ []) with ([14] ++ 6 :: []).
        apply Permutation_cons_app.
        
        (* 7. Match 14 (at head) *)
        apply Permutation_cons.
        
        (* Base case *)
        apply Permutation_nil.
        
      * simpl.
        (* Prove Sortedness *)
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; apply Z.compare_le_iff; simpl; discriminate) ]).
        apply Sorted_nil.
Qed.