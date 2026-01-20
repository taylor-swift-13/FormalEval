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

(* Helper tactics for the proof *)
Ltac split_list a l :=
  match l with
  | a :: ?tl => constr:((@nil Z, tl))
  | ?h :: ?tl => 
      let res := split_list a tl in
      match res with
      | (?l1, ?l2) => constr:((h :: l1, l2))
      end
  end.

Ltac solve_perm :=
  simpl;
  match goal with
  | [ |- Permutation [] [] ] => apply Permutation_nil
  | [ |- Permutation (?a :: ?l) ?r ] =>
      let res := split_list a r in
      match res with
      | (?l1, ?l2) =>
          apply Permutation_trans with (l' := a :: (l1 ++ l2));
          [ apply Permutation_cons; solve_perm 
          | apply Permutation_middle ]
      end
  end.

Example test_case : sort_third_spec 
  [19; 0; -901; 2; 3; -276; 4; 5; 6; 16; 7; 8; 9; 10; 11; 12; 14; 15; 16; 17; 18; 19; 21; 20]
  [2; 0; -901; 4; 3; -276; 9; 5; 6; 12; 7; 8; 16; 10; 11; 16; 14; 15; 19; 17; 18; 19; 21; 20].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check each index up to list length (24) *)
      do 24 (destruct i as [|i]; [
        simpl in H; 
        try (compute in H; congruence);
        simpl; reflexivity
      | ]).
      (* For indices beyond length *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        solve_perm.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [| apply HdRel_nil || (apply HdRel_cons; vm_compute; reflexivity) ]).
        apply Sorted_nil.
Qed.