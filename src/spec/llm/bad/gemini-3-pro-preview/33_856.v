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
  [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; -901; 500; -901]
  [-901; 500; 6; -277; 290; 8; 3; 20; -105; 7; 104; 200; 289; 4; 700; 300; -901; 800; 900; -901; 500; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 22 (destruct i; [ simpl in H; try (exfalso; apply H; reflexivity); simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Target: [-901; -277; 3; 7; 289; 300; 900; 1000] *)
        (* Source: [300; 7; 289; -277; 3; 900; 1000; -901] *)
        eapply Permutation_trans.
        2: { apply Permutation_sym. apply Permutation_middle with (l1:=[300; 7; 289; -277; 3; 900; 1000]) (l2:=[]). }
        simpl. apply Permutation_cons.
        eapply Permutation_trans.
        2: { apply Permutation_sym. apply Permutation_middle with (l1:=[300; 7; 289]) (l2:=[3; 900; 1000]). }
        simpl. apply Permutation_cons.
        eapply Permutation_trans.
        2: { apply Permutation_sym. apply Permutation_middle with (l1:=[300; 7; 289]) (l2:=[900; 1000]). }
        simpl. apply Permutation_cons.
        eapply Permutation_trans.
        2: { apply Permutation_sym. apply Permutation_middle with (l1:=[300]) (l2:=[289; 900; 1000]). }
        simpl. apply Permutation_cons.
        eapply Permutation_trans.
        2: { apply Permutation_sym. apply Permutation_middle with (l1:=[300]) (l2:=[900; 1000]). }
        simpl. apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_cons.
        apply Permutation_nil.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ simpl; try (apply HdRel_cons; lia); try apply HdRel_nil | ]).
        apply Sorted_nil.
Qed.