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

Example test_case : sort_third_spec [9; 0; -1; 6; 105; -5; 3; 12] [3; 0; -1; 6; 105; -5; 9; 12].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for indices 0 to 7. For i >= 8, both are None. *)
      do 8 (destruct i as [|i]; [
        simpl in *;
        try reflexivity;
        try (exfalso; apply H; reflexivity)
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [3; 6; 9] [9; 6; 3] *)
        apply Permutation_trans with (l' := [3; 9; 6]).
        -- apply Permutation_cons. constructor.
        -- apply Permutation_sym.
           change [3; 9; 6] with (3 :: [9; 6] ++ []).
           apply Permutation_cons_app.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons. apply Sorted_nil. apply HdRel_nil.
           ++ apply HdRel_cons. vm_compute. congruence.
        -- apply HdRel_cons. vm_compute. congruence.
Qed.