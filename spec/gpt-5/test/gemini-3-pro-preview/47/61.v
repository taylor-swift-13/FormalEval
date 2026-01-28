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
Example test_median : median_spec [1; 1; 1; 2; 3; 4; 1; 4; 4]%Z (2#1).
Proof.
  (* Unfold the specification *)
  unfold median_spec.
  
  (* Provide the sorted version of the input list *)
  exists [1; 1; 1; 1; 2; 3; 4; 4; 4]%Z.
  
  (* We need to prove 3 things: Permutation, Sorted, and the Result Value *)
  split.
  - (* 1. Prove Permutation *)
    (* Strip the common prefix [1; 1; 1] *)
    do 3 (apply Permutation_cons; [reflexivity | ]).
    (* Prove permutation for the rest: move 1 from middle to head *)
    apply Permutation_cons_app with (l1 := [2; 3; 4]%Z) (l2 := [4; 4]%Z).
    simpl. reflexivity.
    
  - split.
    + (* 2. Prove Sorted *)
      repeat constructor; simpl; try lia.
      
    + (* 3. Prove the Median Calculation *)
      simpl.
      (* length is 9, which is odd. *)
      split.
      * (* Prove index bounds: 4 < 9 *)
        lia.
      * (* Prove value equality: 2#1 = inject_Z (nth 4 ... 0) *)
        simpl.
        reflexivity.
Qed.