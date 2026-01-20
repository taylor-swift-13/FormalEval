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
  [300; 500; 6; 7; 291; 8; -3; 289; 20; 104; -277; 8; 104; 200; -8; 700; 900; -901; 800; 1000; 104; 290; -8]
  [-3; 500; 6; 7; 291; 8; 104; 289; 20; 104; -277; 8; 290; 200; -8; 300; 900; -901; 700; 1000; 104; 800; -8].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check each index individually to avoid issues with abstract indices in large lists *)
      do 23 (destruct i; [ 
        (* For each index 0..22: *)
        (* If i mod 3 = 0, H is a contradiction *)
        try (exfalso; apply H; reflexivity);
        (* If i mod 3 <> 0, values must match *)
        try reflexivity 
      | ]).
      (* For i >= 23, both lists return None *)
      reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; [ simpl; lia | ] || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.