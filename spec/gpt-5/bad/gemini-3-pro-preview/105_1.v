Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Import ListNotations.

Open Scope Z_scope.
Open Scope string_scope.

Definition is_digit (x : Z) : bool :=
  Z.leb 1 x && Z.leb x 9.

Definition to_word (x : Z) : string :=
  if Z.eqb x 1 then "One"
  else if Z.eqb x 2 then "Two"
  else if Z.eqb x 3 then "Three"
  else if Z.eqb x 4 then "Four"
  else if Z.eqb x 5 then "Five"
  else if Z.eqb x 6 then "Six"
  else if Z.eqb x 7 then "Seven"
  else if Z.eqb x 8 then "Eight"
  else "Nine".

Definition by_length_spec (arr : list Z) (ans : list string) : Prop :=
  exists digits_desc,
  Permutation digits_desc (filter is_digit arr) /\
  Sorted Z.ge digits_desc /\
  ans = map to_word digits_desc.

Example test_by_length:
  by_length_spec [2; 1; 1; 4; 5; 8; 2; 3]%Z
                 ["Eight"; "Five"; "Four"; "Three"; "Two"; "Two"; "One"; "One"].
Proof.
  unfold by_length_spec.
  exists [8; 5; 4; 3; 2; 2; 1; 1]%Z.
  split.
  - simpl. (* Evaluates filter *)
    
    (* Move 8 *)
    transitivity (8 :: [2; 1; 1; 4; 5] ++ [2; 3])%list.
    2: { 
      change [2; 1; 1; 4; 5; 8; 2; 3]%Z with ([2; 1; 1; 4; 5] ++ 8 :: [2; 3])%list.
      apply Permutation_cons_app. reflexivity. 
    }
    constructor. simpl.

    (* Move 5 *)
    transitivity (5 :: [2; 1; 1; 4] ++ [2; 3])%list.
    2: { 
      change [2; 1; 1; 4; 5; 2; 3]%Z with ([2; 1; 1; 4] ++ 5 :: [2; 3])%list.
      apply Permutation_cons_app. reflexivity. 
    }
    constructor. simpl.

    (* Move 4 *)
    transitivity (4 :: [2; 1; 1] ++ [2; 3])%list.
    2: { 
      change [2; 1; 1; 4; 2; 3]%Z with ([2; 1; 1] ++ 4 :: [2; 3])%list.
      apply Permutation_cons_app. reflexivity. 
    }
    constructor. simpl.

    (* Move 3 *)
    transitivity (3 :: [2; 1; 1; 2] ++ [])%list.
    2: { 
      change [2; 1; 1; 2; 3]%Z with ([2; 1; 1; 2] ++ 3 :: [])%list.
      apply Permutation_cons_app. reflexivity. 
    }
    constructor. simpl.

    (* Move 2 (first occurrence) *)
    transitivity (2 :: [] ++ [1; 1; 2])%list.
    2: { 
      simpl. apply Permutation_refl.
    }
    constructor. simpl.

    (* Move 2 (second occurrence) *)
    transitivity (2 :: [1; 1] ++ [])%list.
    2: { 
      change [1; 1; 2]%Z with ([1; 1] ++ 2 :: [])%list.
      apply Permutation_cons_app. reflexivity. 
    }
    constructor. simpl.

    (* Remaining elements *)
    apply Permutation_refl.

  - split.
    + (* Sorted *)
      repeat constructor; simpl; try lia.
    + (* Map *)
      simpl. reflexivity.
Qed.