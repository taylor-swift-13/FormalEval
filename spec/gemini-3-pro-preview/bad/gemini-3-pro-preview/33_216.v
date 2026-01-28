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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; 18; -901; 800; 1000; 0; -277; -277]
  [-277; 500; 6; 0; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 300; 18; -901; 800; 1000; 0; 900; -277].
Proof.
  unfold sort_third_spec.
  split.
  - (* length res = length l *)
    simpl. reflexivity.
  - split.
    + (* Preservation of indices not divisible by 3 *)
      intros i H.
      (* The list has 23 elements. We destruct i to check each index concretely. *)
      do 23 (destruct i; [ vm_compute in H; try congruence; reflexivity | ]).
      (* For i >= 23, both lists return None *)
      destruct i; reflexivity.
    + split.
      * (* Permutation of extracted thirds *)
        vm_compute. apply Permutation_refl.
      * (* Sortedness of extracted thirds *)
        vm_compute.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; apply HdRel_cons; vm_compute; intro Hc; discriminate Hc ]).
        apply Sorted_nil.
Qed.