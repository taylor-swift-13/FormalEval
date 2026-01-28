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
  [-2; -5; -7; 2; 10; 0; 9; 5; -3; 2; 8; 3; 7; -5] 
  [-7; -5; -3; 2; -2; 0; 7; 5; 8; 2; 9; 3; 10; -5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* The list has length 14. We destruct i 14 times to handle each index. *)
      do 14 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* Case i >= 14, which contradicts Hlen *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* We need to prove Permutation of even-indexed elements. *)
        (* L_evens = [-2; -7; 10; 9; -3; 8; 7] *)
        (* R_evens = [-7; -3; -2; 7; 8; 9; 10] *)
        
        (* Match -2 *)
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons.
        (* Match -7 *)
        apply Permutation_cons.
        (* Match 10 *)
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons.
        (* Match 9 *)
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons.
        (* Match -3 *)
        apply Permutation_cons.
        (* Match 8 *)
        eapply Permutation_trans. 2: apply Permutation_middle. apply Permutation_cons.
        (* Match 7 *)
        apply Permutation_cons.
        (* Base case *)
        apply Permutation_nil.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.