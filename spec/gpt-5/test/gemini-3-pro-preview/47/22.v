Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.
Open Scope Q_scope.

(* Specification definition *)
Definition median_spec (l : list Z) (m : Q) : Prop :=
  exists sl,
    Permutation sl l /\
    Sorted Z.le sl /\
    let n := length sl in
    let mid := Nat.div n 2 in
    (if Nat.odd n
     then Nat.lt mid n /\ m = inject_Z (nth mid sl 0%Z)
     else Nat.le 2 n /\ Nat.lt mid n /\
          m = (inject_Z (nth (Nat.pred mid) sl 0%Z) + inject_Z (nth mid sl 0%Z)) / (2#1)).

(* Test case *)
Example test_median : median_spec [1; 1; 1; 2; 2; 3; 4; 1; 1]%Z (1#1).
Proof.
  (* Unfold the specification *)
  unfold median_spec.
  
  (* Provide the sorted version of the input list *)
  exists [1; 1; 1; 1; 1; 2; 2; 3; 4]%Z.
  
  split.
  - (* Prove Permutation *)
    (* We skip the first 3 common elements: 1, 1, 1 *)
    do 3 apply perm_skip.
    (* We need to show [1; 1; 2; 2; 3; 4] is a permutation of [2; 2; 3; 4; 1; 1] *)
    apply Permutation_sym.
    (* Rewrite lists as concatenations to use Permutation_app_comm *)
    change [2; 2; 3; 4; 1; 1]%Z with ([2; 2; 3; 4] ++ [1; 1])%Z.
    change [1; 1; 2; 2; 3; 4]%Z with ([1; 1] ++ [2; 2; 3; 4])%Z.
    apply Permutation_app_comm.
    
  - split.
    + (* Prove Sorted *)
      repeat constructor; simpl; try lia.
      
    + (* Prove the Median Calculation *)
      simpl.
      split.
      * (* Prove index bounds *)
        lia.
      * (* Prove value equality *)
        reflexivity.
Qed.