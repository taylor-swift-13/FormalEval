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
  [5; -2; -12; 11; 4; 4; 23; 2; 4; 3; 11; 12; -10] 
  [-12; -2; -10; 11; 4; 4; 4; 2; 5; 3; 11; 12; 23].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length *)
    simpl. reflexivity.
  - split.
    + (* Odd indices *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in *; try discriminate; try reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation *)
        simpl.
        (* Current: [5; -12; 4; 23; 4; 11; -10] *)
        (* Target:  [-12; -10; 4; 4; 5; 11; 23] *)
        
        (* Move 5 *)
        apply Permutation_trans with (l' := 5 :: [-12; -10; 4; 4; 11; 23]).
        { apply Permutation_cons.
          (* Current: [-12; 4; 23; 4; 11; -10], Target tail: [-12; -10; 4; 4; 11; 23] *)
          apply Permutation_cons.
          (* Current: [4; 23; 4; 11; -10], Target tail: [-10; 4; 4; 11; 23] *)
          
          (* Move 4 *)
          apply Permutation_trans with (l' := 4 :: [-10; 4; 11; 23]).
          { apply Permutation_cons.
            (* Current: [23; 4; 11; -10], Target tail: [-10; 4; 11; 23] *)
            
            (* Move 23 *)
            apply Permutation_trans with (l' := 23 :: [-10; 4; 11]).
            { apply Permutation_cons.
              (* Current: [4; 11; -10], Target tail: [-10; 4; 11] *)
              
              (* Move 4 *)
              apply Permutation_trans with (l' := 4 :: [-10; 11]).
              { apply Permutation_cons.
                (* Current: [11; -10], Target tail: [-10; 11] *)
                
                (* Move 11 *)
                apply Permutation_trans with (l' := 11 :: [-10]).
                { apply Permutation_cons. apply Permutation_refl. }
                { apply Permutation_sym. apply Permutation_cons_app with (l1 := [-10]) (l2 := []). reflexivity. }
              }
              { apply Permutation_sym. apply Permutation_cons_app with (l1 := [-10]) (l2 := [11]). reflexivity. }
            }
            { apply Permutation_sym. apply Permutation_cons_app with (l1 := [-10; 4; 11]) (l2 := []). reflexivity. }
          }
          { apply Permutation_sym. apply Permutation_cons_app with (l1 := [-10]) (l2 := [4; 11; 23]). reflexivity. }
        }
        { apply Permutation_sym. apply Permutation_cons_app with (l1 := [-12; -10; 4; 4]) (l2 := [11; 23]). reflexivity. }
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | try apply HdRel_nil; try (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.