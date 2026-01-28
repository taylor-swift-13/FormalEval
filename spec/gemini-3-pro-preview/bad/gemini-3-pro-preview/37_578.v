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
  [-3; 1; 1; 1; 2; 2; 1; 2; 2; 13; 1; 1; 1] 
  [-3; 1; 1; 1; 1; 2; 1; 2; 1; 13; 2; 1; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We handle indices 0 to 12 by repeated destruction. 
         This avoids large proof terms and timeouts compared to pure computation or lia. *)
      do 13 (destruct i; [
        try (simpl in Hodd; discriminate); (* Even indices: odd i = false *)
        try (simpl; reflexivity)           (* Odd indices: values match *)
      | ]).
      (* Remaining case: i >= 13 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [-3; 1; 2; 1; 2; 1; 1] [-3; 1; 1; 1; 1; 2; 2] *)
        apply Permutation_cons; [reflexivity|]. (* Match -3 *)
        apply Permutation_cons; [reflexivity|]. (* Match 1 *)
        
        (* Current: [2; 1; 2; 1; 1] ~ [1; 1; 1; 2; 2] *)
        (* Swap first two elements to bring 1 to front *)
        transitivity (1 :: 2 :: 2 :: 1 :: 1).
        { constructor. }
        apply Permutation_cons; [reflexivity|]. (* Match 1 *)
        
        (* Current: [2; 2; 1; 1] ~ [1; 1; 2; 2] *)
        (* Move 1 from end of list to front *)
        transitivity (1 :: 2 :: 2 :: 1).
        { symmetry. apply Permutation_middle with (l1 := [2; 2]). }
        apply Permutation_cons; [reflexivity|]. (* Match 1 *)
        
        (* Current: [2; 2; 1] ~ [1; 2; 2] *)
        (* Move 1 from end to front *)
        transitivity (1 :: 2 :: 2).
        { symmetry. apply Permutation_middle with (l1 := [2; 2]). }
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (constructor; [try lia | ]).
        apply HdRel_nil.
Qed.