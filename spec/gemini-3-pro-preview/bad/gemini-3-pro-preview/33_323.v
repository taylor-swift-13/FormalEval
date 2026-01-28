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
  [-4; 8; 4; -6; 0; -8; 6; 2; 1; 8; 13; 6; 6; -8; 14; -6; 8] 
  [-6; 8; 4; -6; 0; -8; -4; 2; 1; 6; 13; 6; 6; -8; 14; 8; 8].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Since the list is finite and concrete, we can check each index.
         For indices divisible by 3, H yields a contradiction.
         For others, the values match. *)
      do 17 (destruct i; [ simpl in *; try (exfalso; apply H; reflexivity); try reflexivity | ]).
      (* For indices beyond the list length, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* We use a tactic to prove permutation of concrete lists by finding elements *)
        repeat (
          match goal with
          | |- Permutation [] [] => apply Permutation_nil
          | |- Permutation (?x :: ?xs) ?l =>
              eapply perm_trans; [ | apply Permutation_Add; solve [ repeat constructor ] ];
              apply Permutation_cons
          end).
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* We use a tactic to prove Sorted by checking HdRel for each step *)
        repeat (apply Sorted_cons; [ | simpl; first [ apply HdRel_nil | apply HdRel_cons; vm_compute; discriminate ] ]).
        apply Sorted_nil.
Qed.