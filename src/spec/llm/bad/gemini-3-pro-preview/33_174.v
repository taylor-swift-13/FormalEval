Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [19; 0; -901; 2; 3; 4; 5; 6; 16; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 21; 20]
  [2; 0; -901; 5; 3; 4; 7; 6; 16; 10; 8; 9; 14; 11; 12; 17; 15; 16; 19; 18; 19; 21; 20].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 23 (destruct i; [
        vm_compute in H; try congruence; vm_compute; reflexivity 
      | ]).
      vm_compute. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        apply NoDup_Permutation.
        -- repeat constructor; simpl; try tauto.
        -- repeat constructor; simpl; try tauto.
        -- intros x; simpl; intuition.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [
          simpl; try apply HdRel_nil; apply HdRel_cons; lia 
        | ]).
        apply Sorted_nil.
Qed.