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

Example test_case : sort_third_spec 
  [10; 9; 8; 7; 6; 5; 4; 3; 2; 1; -1; -2; -3; -4; -5; -6; -7; -8; -9; -10; -8] 
  [-9; 9; 8; -6; 6; 5; -3; 3; 2; 1; -1; -2; 4; -4; -5; 7; -7; -8; 10; -10; -8].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Handle all relevant indices by case analysis *)
      do 22 (destruct i; [
        simpl in *;
        try reflexivity;
        try (exfalso; compute in H; congruence)
      | ]).
      (* Handle out-of-bounds indices *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* The extracted list from res is the reverse of the one from l *)
        eapply Permutation_trans.
        2: apply Permutation_rev.
        reflexivity.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [
          simpl; match goal with
          | |- HdRel _ _ _ [] => apply HdRel_nil
          | |- HdRel _ _ _ _ => apply HdRel_cons; simpl; lia
          end
        | ]).
        apply Sorted_nil.
Qed.