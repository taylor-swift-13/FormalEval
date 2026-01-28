Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 21; -105; -277; 104; 200; 4; 5; 700; 900; -200; -901; 800; 1000; 300] 
  [-200; 500; 6; 5; 8; 289; 7; -105; -277; 21; 200; 4; 104; 700; 900; 300; -901; 800; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check indices up to length of list *)
      do 21 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        (* Prove Permutation by explicitly swapping elements to match sorted order *)
        (* Target: [300; 7; 21; 104; 5; -200; 1000] *)
        (* Sorted: [-200; 5; 7; 21; 104; 300; 1000] *)
        
        (* Move -200 *)
        apply Permutation_trans with (l' := -200 :: [300; 7; 21; 104; 5; 1000]).
        { apply Permutation_skip.
          (* Move 5 *)
          apply Permutation_trans with (l' := 5 :: [300; 7; 21; 104; 1000]).
          { apply Permutation_skip.
            (* Move 7 *)
            apply Permutation_trans with (l' := 7 :: [300; 21; 104; 1000]).
            { apply Permutation_skip.
              (* Move 21 *)
              apply Permutation_trans with (l' := 21 :: [300; 104; 1000]).
              { apply Permutation_skip.
                (* Move 104 *)
                apply Permutation_trans with (l' := 104 :: [300; 1000]).
                { apply Permutation_skip.
                  (* 300 and 1000 match *)
                  apply Permutation_skip.
                  apply Permutation_skip.
                  apply Permutation_nil.
                }
                { apply Permutation_middle with (l1 := [300]). }
              }
              { apply Permutation_middle with (l1 := [300]). }
            }
            { apply Permutation_middle with (l1 := [300]). }
          }
          { apply Permutation_middle with (l1 := [300; 7; 21; 104]). }
        }
        { apply Permutation_middle with (l1 := [300; 7; 21; 104; 5]). }
      * simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.