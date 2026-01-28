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
Example test_median : median_spec [0; 0; 0; 1]%Z (0#2).
Proof.
  (* Unfold the specification *)
  unfold median_spec.
  
  (* Provide the sorted version of the input list *)
  exists [0; 0; 0; 1]%Z.
  
  (* We need to prove 3 things: Permutation, Sorted, and the Result Value *)
  split.
  - (* 1. Prove Permutation *)
    (* The list is already sorted, so it is a permutation of itself *)
    reflexivity.
    
  - split.
    + (* 2. Prove Sorted *)
      (* Step through the list constructors to prove ordering *)
      repeat constructor; simpl; try lia.
      
    + (* 3. Prove the Median Calculation *)
      (* Simplify the length and mid calculations *)
      simpl.
      (* length is 4, which is even. The 'if' expression evaluates to the 'else' branch. *)
      split.
      * (* Prove index bounds: 2 <= 4 *)
        lia.
      * split.
        -- (* Prove index bounds: 2 < 4 *)
           lia.
        -- (* Prove value equality: 0#2 = (inject_Z 0 + inject_Z 0) / (2#1) *)
           (* Note: The specification results in an unreduced fraction 0#2, so we match that. *)
           simpl.
           reflexivity.
Qed.