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
  [0; 3; -5; 2; -3; 3; -8; 0; 123; 1; -10; -5] 
  [-10; 3; -8; 2; -5; 3; -3; 0; 0; 1; 123; -5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen; lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [0; -5; -3; -8; 123; -10] [-10; -8; -5; -3; 0; 123] *)
        
        (* Move -10 to front *)
        etransitivity.
        { apply Permutation_sym. apply (Permutation_middle _ [0; -5; -3; -8; 123] [] (-10)). }
        simpl. apply perm_skip.
        
        (* Move -8 to front *)
        etransitivity.
        { apply Permutation_sym. apply (Permutation_middle _ [0; -5; -3] [123] (-8)). }
        simpl. apply perm_skip.
        
        (* Move -5 to front *)
        etransitivity.
        { apply Permutation_sym. apply (Permutation_middle _ [0] [-3; 123] (-5)). }
        simpl. apply perm_skip.
        
        (* Move -3 to front *)
        etransitivity.
        { apply Permutation_sym. apply (Permutation_middle _ [0] [123] (-3)). }
        simpl. apply perm_skip.
        
        (* Remaining [0; 123] matches [0; 123] *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil || (simpl; lia)).
Qed.