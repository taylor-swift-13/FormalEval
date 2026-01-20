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
  [1; 2; 3; 5; -9; 1; 0; -8; 9; -12; 7; -4; 6; 1; 6; 3] 
  [-12; 2; 3; 0; -9; 1; 1; -8; 9; 3; 7; -4; 5; 1; 6; 6].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i enough times to cover the list length (16) *)
      do 17 (destruct i; [
        simpl in *;
        (* If i mod 3 == 0, the hypothesis H (i mod 3 <> 0) is contradictory *)
        try (match goal with | H : _ <> 0 |- _ => exfalso; apply H; reflexivity end);
        (* If i mod 3 != 0, check that values match *)
        try reflexivity
      | ]).
      (* For indices out of bounds, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Since lists are concrete and have no duplicates, use NoDup_Permutation *)
        apply NoDup_Permutation.
        -- (* NoDup res_extracted *)
           repeat (constructor; [ simpl; intro Hin; intuition congruence | ]). apply NoDup_nil.
        -- (* NoDup l_extracted *)
           repeat (constructor; [ simpl; intro Hin; intuition congruence | ]). apply NoDup_nil.
        -- (* Element equivalence *)
           intros x. simpl. intuition; subst; auto 10.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Check sortedness for concrete list *)
        repeat (apply Sorted_cons; [ | 
          match goal with
          | |- HdRel _ _ [] => apply HdRel_nil
          | |- HdRel _ _ (_ :: _) => apply HdRel_cons; [ unfold Z.le; simpl; intro Hc; discriminate ]
          end ]).
        apply Sorted_nil.
Qed.