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
Example test_median : median_spec [14; 1; 3; 7; 8; 10; 10]%Z (8#1).
Proof.
  (* Unfold the specification *)
  unfold median_spec.
  
  (* Provide the sorted version of the input list *)
  exists [1; 3; 7; 8; 10; 10; 14]%Z.
  
  (* We need to prove 3 things: Permutation, Sorted, and the Result Value *)
  split.
  - (* 1. Prove Permutation *)
    (* We show that [1; 3; 7; 8; 10; 10; 14] is a permutation of [14; 1; 3; 7; 8; 10; 10] *)
    apply Permutation_sym.
    (* Use the lemma that allows moving the head element '14' to the end *)
    apply Permutation_cons_app with (l1 := [1; 3; 7; 8; 10; 10]%Z) (l2 := []%Z).
    simpl. reflexivity.
    
  - split.
    + (* 2. Prove Sorted *)
      (* Step through the list constructors to prove ordering *)
      repeat constructor; simpl; try lia.
      
    + (* 3. Prove the Median Calculation *)
      (* Simplify the length and mid calculations *)
      simpl.
      (* length is 7, which is odd. The 'if' expression evaluates to the 'then' branch. *)
      split.
      * (* Prove index bounds: 3 < 7 *)
        lia.
      * (* Prove value equality: 8#1 = inject_Z (nth 3 ... 0) *)
        (* nth 3 [1; 3; 7; 8; 10; 10; 14] 0 evaluates to 8 *)
        simpl.
        reflexivity.
Qed.