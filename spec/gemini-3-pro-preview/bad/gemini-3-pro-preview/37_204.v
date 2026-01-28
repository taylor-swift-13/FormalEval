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
  [5; 3; -5; 2; -3; -2; -9; 0; 123; 1; -10; -9] 
  [-10; 3; -9; 2; -5; -2; -3; 0; 5; 1; 123; -9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        transitivity (5 :: [-10; -9; -5; -3] ++ [123]); [ apply perm_skip | apply (Permutation_middle Z [-10; -9; -5; -3] [123] 5) ].
        transitivity (-5 :: [-10; -9] ++ [-3; 123]); [ apply perm_skip | apply (Permutation_middle Z [-10; -9] [-3; 123] (-5)) ].
        transitivity (-3 :: [-10; -9] ++ [123]); [ apply perm_skip | apply (Permutation_middle Z [-10; -9] [123] (-3)) ].
        transitivity (-9 :: [-10] ++ [123]); [ apply perm_skip | apply (Permutation_middle Z [-10] [123] (-9)) ].
        transitivity (123 :: [-10] ++ []); [ apply perm_skip | apply (Permutation_middle Z [-10] [] 123) ].
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.