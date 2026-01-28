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

Example test_case : sort_third_spec [9; 0; -1; 6; 3; 12; 6] [6; 0; -1; 6; 3; 12; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Check first 7 indices *)
      do 7 (destruct i as [|i]; [ simpl in *; try (elim H; reflexivity); try reflexivity | ]).
      (* For i >= 7, both are None *)
      simpl. reflexivity.
    + split.
      * (* Permutation of extracted thirds: [6; 6; 9] vs [9; 6; 6] *)
        simpl.
        apply Permutation_trans with (l' := [6; 9; 6]).
        -- apply perm_skip. apply perm_swap.
        -- apply perm_swap.
      * (* Sortedness of extracted thirds: [6; 6; 9] *)
        simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ apply HdRel_cons. unfold Z.le; simpl; intro Hc; discriminate.
        -- apply HdRel_cons. apply Z.le_refl.
Qed.