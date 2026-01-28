Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive strange_interleave : list Z -> list Z -> Prop :=
| si_nil : strange_interleave [] []
| si_one : forall x, strange_interleave [x] [x]
| si_step : forall x y mid res,
    strange_interleave mid res ->
    strange_interleave (x :: mid ++ [y]) (x :: y :: res).

Definition strange_sort_list_spec (lst : list Z) (ans : list Z) : Prop :=
  exists sorted_lst,
    Permutation lst sorted_lst /\
    Sorted Z.le sorted_lst /\
    strange_interleave sorted_lst ans.

Example test_case : strange_sort_list_spec [1; 2; 3; 4] [1; 4; 2; 3].
Proof.
  (* Unfold the specification *)
  unfold strange_sort_list_spec.
  
  (* Provide the sorted version of the input list as the witness *)
  exists [1; 2; 3; 4].
  
  (* We need to prove 3 things: Permutation, Sorted, and strange_interleave *)
  split.
  
  (* 1. Prove Permutation *)
  - apply Permutation_refl.
  
  - split.
    (* 2. Prove Sorted *)
    + repeat constructor; try lia.
    
    (* 3. Prove strange_interleave *)
    + (* Step 1: Decompose [1; 2; 3; 4] into 1 :: [2; 3] ++ [4] *)
      change [1; 2; 3; 4] with (1 :: [2; 3] ++ [4]).
      apply si_step.
      
      (* Step 2: Decompose [2; 3] into 2 :: [] ++ [3] *)
      change [2; 3] with (2 :: [] ++ [3]).
      apply si_step.
      
      (* Step 3: Base case *)
      apply si_nil.
Qed.