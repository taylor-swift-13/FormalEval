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
  [5; -3; 3; -5; 2; -3; 3; -9; 0; 123; 1; -10; 10; -5; 3] 
  [0; -3; 1; -5; 2; -3; 3; -9; 3; 123; 3; -10; 5; -5; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 15 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Input evens: [5; 3; 2; 3; 0; 1; 10; 3] *)
        (* Target evens: [0; 1; 2; 3; 3; 3; 5; 10] *)
        
        (* Move 0 *)
        eapply Permutation_trans. apply Permutation_sym. 
        apply (Permutation_middle _ [5; 3; 2; 3] [1; 10; 3] 0). 
        apply Permutation_cons.

        (* Move 1 *)
        eapply Permutation_trans. apply Permutation_sym. 
        apply (Permutation_middle _ [5; 3; 2; 3] [10; 3] 1). 
        apply Permutation_cons.

        (* Move 2 *)
        eapply Permutation_trans. apply Permutation_sym. 
        apply (Permutation_middle _ [5; 3] [3; 10; 3] 2). 
        apply Permutation_cons.

        (* Move 3 *)
        eapply Permutation_trans. apply Permutation_sym. 
        apply (Permutation_middle _ [5] [3; 10; 3] 3). 
        apply Permutation_cons.

        (* Move 3 *)
        eapply Permutation_trans. apply Permutation_sym. 
        apply (Permutation_middle _ [5] [10; 3] 3). 
        apply Permutation_cons.

        (* Move 3 *)
        eapply Permutation_trans. apply Permutation_sym. 
        apply (Permutation_middle _ [5; 10] [] 3). 
        apply Permutation_cons.

        (* Remaining [5; 10] matches [5; 10] *)
        apply Permutation_refl.

      * (* 4. Sorted check *)
        simpl.
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.