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
Example test_median : median_spec [3; 1; 2; 4; 5]%Z (3#1).
Proof.
  (* Unfold the specification *)
  unfold median_spec.
  
  (* Provide the sorted version of the input list *)
  exists [1; 2; 3; 4; 5]%Z.
  
  (* We need to prove 3 things: Permutation, Sorted, and the Result Value *)
  split.
  - (* 1. Prove Permutation *)
    (* We show that [1; 2; 3; 4; 5] is a permutation of [3; 1; 2; 4; 5] *)
    apply Permutation_sym.
    (* Use the lemma that allows moving the head element '3' into the middle *)
    apply Permutation_cons_app with (l1 := [1; 2]%Z) (l2 := [4; 5]%Z).
    simpl. reflexivity.
    
  - split.
    + (* 2. Prove Sorted *)
      (* Step through the list constructors to prove ordering *)
      repeat constructor; simpl; try lia.
      
    + (* 3. Prove the Median Calculation *)
      (* Simplify the length and mid calculations *)
      simpl.
      (* length is 5, which is odd. The 'if' expression evaluates to the 'then' branch. *)
      split.
      * (* Prove index bounds: 2 < 5 *)
        lia.
      * (* Prove value equality: 3#1 = inject_Z (nth 2 ... 0) *)
        (* nth 2 [1; 2; 3; 4; 5] 0 evaluates to 3 *)
        simpl.
        reflexivity.
Qed.