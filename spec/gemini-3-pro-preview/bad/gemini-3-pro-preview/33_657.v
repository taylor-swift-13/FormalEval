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
  [500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; 105] 
  [-901; 6; 7; 4; 8; 289; 20; -105; -277; 104; 200; 3; 105; 700; 900; 290; 800; 1000; 500].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Handle indices 0 to 18 explicitly to avoid timeout with symbolic evaluation *)
      do 19 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity);
        reflexivity
      | ]).
      (* i >= 19 *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        assert (forall (l1 l2 : list Z) (x : Z), Permutation (l1 ++ x :: l2) (x :: l1 ++ l2)) as move_front.
        { intros. apply Permutation_sym. apply Permutation_middle. }

        (* Target: [-901; 4; 20; 104; 105; 290; 500] *)
        (* Source: [500; 290; 20; 104; 4; -901; 105] *)

        (* Move -901 *)
        apply Permutation_trans with (l' := -901 :: [500; 290; 20; 104; 4] ++ [105]).
        { change [500; 290; 20; 104; 4; -901; 105] with ([500; 290; 20; 104; 4] ++ -901 :: [105]).
          apply move_front. }
        apply Permutation_cons.
        
        (* Move 4 *)
        apply Permutation_trans with (l' := 4 :: [500; 290; 20; 104] ++ [105]).
        { change ([500; 290; 20; 104; 4] ++ [105]) with ([500; 290; 20; 104] ++ 4 :: [105]).
          apply move_front. }
        apply Permutation_cons.

        (* Move 20 *)
        apply Permutation_trans with (l' := 20 :: [500; 290] ++ [104; 105]).
        { change ([500; 290; 20; 104] ++ [105]) with ([500; 290] ++ 20 :: [104; 105]).
          apply move_front. }
        apply Permutation_cons.

        (* Move 104 *)
        apply Permutation_trans with (l' := 104 :: [500; 290] ++ [105]).
        { change ([500; 290] ++ [104; 105]) with ([500; 290] ++ 104 :: [105]).
          apply move_front. }
        apply Permutation_cons.

        (* Move 105 *)
        apply Permutation_trans with (l' := 105 :: [500; 290] ++ []).
        { change ([500; 290] ++ [105]) with ([500; 290] ++ 105 :: []).
          apply move_front. }
        apply Permutation_cons.

        (* [500; 290] -> [290; 500] *)
        apply Permutation_swap.

      * (* Sorted *)
        simpl.
        repeat (constructor; [| try apply HdRel_nil]).
        all: simpl; try lia.
Qed.