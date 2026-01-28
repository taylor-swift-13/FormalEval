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
  [1; 2; 3; -3; 5; 16; -278; 15; 16; -8; 10; -12; 7; 0; -12; 5; 10] 
  [-278; 2; 3; -8; 5; 16; -3; 15; 16; 1; 10; -12; 5; 0; -12; 7; 10].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check indices 0 to 16 explicitly using destruct *)
      do 17 (destruct i as [|i]; [
        simpl in *;
        try (exfalso; vm_compute in H; congruence); (* Case divisible by 3: contradiction *)
        try reflexivity (* Case not divisible: must match *)
      | ]).
      (* Case i >= 17: both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Use NoDup strategy to prove permutation of concrete lists *)
        apply NoDup_Permutation.
        -- (* NoDup res_thirds *)
           repeat constructor; simpl; try tauto; try discriminate.
        -- (* NoDup l_thirds *)
           repeat constructor; simpl; try tauto; try discriminate.
        -- (* Elements equivalence *)
           intros x. simpl. tauto.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Construct Sorted proof by checking all cons and HdRel constraints *)
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_nil || apply HdRel_cons).
        (* Verify Z.le for all generated HdRel goals *)
        all: simpl; try apply Z.leb_le; try vm_compute; try reflexivity.
Qed.