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
  [1; 2; 3; -3; 3; 1; 5; 2; 11; 0; -8; 105; 9; -12; 7; 6; 2; -3] 
  [-3; 2; 3; 0; 3; 1; 1; 2; 11; 5; -8; 105; 6; -12; 7; 9; 2; -3].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 17 explicitly *)
      do 18 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      (* For i >= 18, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply NoDup_Permutation.
        -- repeat constructor; simpl; try tauto.
        -- repeat constructor; simpl; try tauto.
        -- intros x. simpl. tauto.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* List: [-3; 0; 1; 5; 6; 9] *)
        apply Sorted_cons. 2: { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons. 2: { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons. 2: { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons. 2: { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons. 2: { apply HdRel_cons. apply Z.leb_le. reflexivity. }
        apply Sorted_cons. 2: { apply HdRel_nil. }
        apply Sorted_nil.
Qed.