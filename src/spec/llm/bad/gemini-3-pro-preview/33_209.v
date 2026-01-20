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
  [300; 500; 6; 7; 200; 7; 289; -105; -277; 104; 200; 3; 4; 5; 700; 900; -200; -901; 800; 1000; 6]
  [4; 500; 6; 7; 200; 7; 104; -105; -277; 289; 200; 3; 300; 5; 700; 800; -200; -901; 900; 1000; 6].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 21 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity); (* if i mod 3 = 0, contradiction *)
        try reflexivity (* if i mod 3 <> 0, values match *)
      | ]).
      (* For i >= 21 *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        (* Goal: Permutation [4; 7; 104; 289; 300; 800; 900] [300; 7; 289; 104; 4; 900; 800] *)
        transitivity (4 :: [300; 7; 289; 104; 900; 800]).
        { change [300; 7; 289; 104; 4; 900; 800] with ([300; 7; 289; 104] ++ 4 :: [900; 800]).
          apply Permutation_sym, Permutation_middle. }
        constructor.
        transitivity (7 :: [300; 289; 104; 900; 800]).
        { change [300; 7; 289; 104; 900; 800] with ([300] ++ 7 :: [289; 104; 900; 800]).
          apply Permutation_sym, Permutation_middle. }
        constructor.
        transitivity (104 :: [300; 289; 900; 800]).
        { change [300; 289; 104; 900; 800] with ([300; 289] ++ 104 :: [900; 800]).
          apply Permutation_sym, Permutation_middle. }
        constructor.
        transitivity (289 :: [300; 900; 800]).
        { change [300; 289; 900; 800] with ([300] ++ 289 :: [900; 800]).
          apply Permutation_sym, Permutation_middle. }
        constructor.
        (* Remaining: Permutation [300; 800; 900] [300; 900; 800] *)
        constructor.
        apply Permutation_swap.
      * (* Sorted *)
        simpl.
        repeat apply Sorted_cons.
        all: try apply Sorted_nil.
        all: try apply HdRel_nil.
        all: try (simpl; apply HdRel_cons; compute; intro H; discriminate).
Qed.