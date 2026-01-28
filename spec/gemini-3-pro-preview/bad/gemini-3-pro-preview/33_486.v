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
  [19; 0; -901; 2; 3; 4; 5; 6; 7; 8; 10; 11; 9; 12; 13; 14; 15; 11; 16; 17; 18; 19; 21; 20; 0] 
  [0; 0; -901; 2; 3; 4; 5; 6; 7; 8; 10; 11; 9; 12; 13; 14; 15; 11; 16; 17; 18; 19; 21; 20; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. indices *)
      intros i H.
      assert (Hlen: (i < 25 \/ 25 <= i)%nat) by lia.
      destruct Hlen as [Hlt|Hge].
      * (* i < 25 *)
        repeat (destruct i as [|i]; [
          simpl in *;
          try (exfalso; lia); (* H contradicts i mod 3 = 0 *)
          try reflexivity     (* values match *)
        | ]).
        exfalso; lia.
      * (* i >= 25 *)
        rewrite !nth_error_None.
        all: simpl; try lia.
        reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        (* Goal: Permutation [0; ...; 19; 19] [19; ...; 19; 0] *)
        apply Permutation_sym.
        (* RHS is [19; ...; 0], treat as [19; ...; 19] ++ [0] *)
        change [19; 2; 5; 8; 9; 14; 16; 19; 0] with ([19; 2; 5; 8; 9; 14; 16; 19] ++ [0]).
        (* Move 0 to front *)
        transitivity ([0] ++ [19; 2; 5; 8; 9; 14; 16; 19]).
        { apply Permutation_app_comm. }
        simpl. apply Permutation_cons.
        (* Goal: Permutation [19; 2; 5; 8; 9; 14; 16; 19] [2; 5; 8; 9; 14; 16; 19; 19] *)
        (* LHS is [19] ++ [2; ...; 19] *)
        change [19; 2; 5; 8; 9; 14; 16; 19] with ([19] ++ [2; 5; 8; 9; 14; 16; 19]).
        (* RHS is [2; ...; 19] ++ [19] *)
        change [2; 5; 8; 9; 14; 16; 19; 19] with ([2; 5; 8; 9; 14; 16; 19] ++ [19]).
        apply Permutation_app_comm.
      * (* 4. Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try lia ]).
        apply Sorted_nil.
Qed.