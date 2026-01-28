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
  [300; 1; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -902; 800; 1000; 103; 1001] 
  [-902; 1; 7; 4; 8; 289; 20; -105; -277; 103; 200; 3; 104; 700; 900; 290; 800; 1000; 300; 1001].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. Length equality *)
    simpl. reflexivity.
  - split.
    + (* 2. Indices not divisible by 3 *)
      intros i H.
      (* Deconstruct i to check each index explicitly. 
         This avoids timeouts with large reflexivity checks. *)
      do 20 (destruct i as [|i]; 
             [ simpl in H; 
               try (exfalso; vm_compute in H; apply H; reflexivity);
               simpl; reflexivity 
             | ]).
      (* Case i >= 20, both nth_error are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of thirds *)
        simpl.
        apply NoDup_Permutation.
        -- (* NoDup of result thirds *)
           repeat constructor; simpl; intuition discriminate.
        -- (* NoDup of input thirds *)
           repeat constructor; simpl; intuition discriminate.
        -- (* Elements equivalence *)
           intros x. simpl. tauto.
      * (* 4. Sortedness of result thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (vm_compute; reflexivity) ]).
        apply Sorted_nil.
Qed.