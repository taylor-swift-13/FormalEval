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
  [500; 6; 6; 8; 289; 20; 8; -277; 104; 200; 3; 20; 300; 4; 5; 700; 900; -200; -901; 800; 1000; -277] 
  [-901; 6; 6; -277; 289; 20; 8; -277; 104; 8; 3; 20; 200; 4; 5; 300; 900; -200; 500; 800; 1000; 700].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 22 (destruct i; [ simpl in H; try congruence; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        apply Permutation_sym.
        (* Target: [-901; -277; 8; 8; 200; 300; 500; 700] *)
        (* Current: [500; 8; 8; 200; 300; 700; -901; -277] *)
        (* 1. Move -901 *)
        apply Permutation_trans with (l' := -901 :: [500; 8; 8; 200; 300; 700] ++ [-277]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* 2. Move -277 *)
        apply Permutation_trans with (l' := -277 :: [500; 8; 8; 200; 300; 700] ++ []).
        { rewrite app_nil_r. apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* 3. Move 8 *)
        apply Permutation_trans with (l' := 8 :: [500] ++ [8; 200; 300; 700]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* 4. Move 8 *)
        apply Permutation_trans with (l' := 8 :: [500] ++ [200; 300; 700]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* 5. Move 200 *)
        apply Permutation_trans with (l' := 200 :: [500] ++ [300; 700]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* 6. Move 300 *)
        apply Permutation_trans with (l' := 300 :: [500] ++ [700]).
        { apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_cons.
        (* 7. Tail *)
        apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; apply HdRel_cons; compute; intro Hc; discriminate Hc ]).
        apply Sorted_nil.
Qed.