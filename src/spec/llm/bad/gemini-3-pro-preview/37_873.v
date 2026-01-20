Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [-11; 5; 0; 5; 5; 0; 6; 0; 5; 5; 0; 4; 0] 
  [-11; 5; 0; 5; 0; 0; 0; 0; 5; 5; 5; 4; 6].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* Check all indices 0..12 *)
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* i >= 13, out of bounds *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [-11; 0; 5; 6; 5; 0; 0] [-11; 0; 0; 0; 5; 5; 6] *)
        apply Permutation_cons. (* Match -11 *)
        apply Permutation_cons. (* Match 0 *)
        
        (* Current LHS: [5; 6; 5; 0; 0] *)
        (* Current RHS: [0; 0; 5; 5; 6] *)
        
        (* Need to bring 5 to head of RHS. 5 is at index 2 in RHS. *)
        (* RHS = [0; 0] ++ 5 :: [5; 6] *)
        transitivity (5 :: [0; 0] ++ [5; 6]).
        { apply Permutation_middle. }
        apply Permutation_cons. (* Match 5 *)
        
        (* Current LHS: [6; 5; 0; 0] *)
        (* Current RHS: [0; 0; 5; 6] *)
        
        (* Need to bring 6 to head of RHS. 6 is at index 3 in RHS. *)
        (* RHS = [0; 0; 5] ++ 6 :: [] *)
        transitivity (6 :: [0; 0; 5] ++ []).
        { apply Permutation_middle. }
        apply Permutation_cons. (* Match 6 *)
        
        (* Current LHS: [5; 0; 0] *)
        (* Current RHS: [0; 0; 5] *)
        
        (* Need to bring 5 to head of RHS. 5 is at index 2 in RHS. *)
        (* RHS = [0; 0] ++ 5 :: [] *)
        transitivity (5 :: [0; 0] ++ []).
        { apply Permutation_middle. }
        apply Permutation_cons. (* Match 5 *)
        
        (* Current LHS: [0; 0] *)
        (* Current RHS: [0; 0] *)
        apply Permutation_cons. (* Match 0 *)
        apply Permutation_cons. (* Match 0 *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_cons; lia ]).
        apply Sorted_nil.
Qed.