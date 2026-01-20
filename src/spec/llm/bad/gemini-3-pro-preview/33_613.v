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

Example test_case : sort_third_spec [300; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 300; 3; 4; 5; 700; 900; -901; 800; 1000; -901] [-901; 500; 6; -901; 290; 8; -277; 20; -105; 5; 104; 200; 7; 3; 4; 289; 700; 900; 300; 800; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Handle the finite number of indices explicitly *)
      repeat (destruct i; [ simpl in H; try contradiction; simpl; reflexivity | ]).
      (* For i >= 22, both lists are exhausted *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        vm_compute.
        (* Target (LHS): [-901; -901; -277; 5; 7; 289; 300; 300] *)
        (* Source (RHS): [300; 7; 289; -277; 300; 5; -901; -901] *)
        
        (* 1. Move first -901 to front *)
        apply Permutation_trans with (l' := -901 :: [300; 7; 289; -277; 300; 5] ++ [-901]).
        { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        
        (* 2. Move second -901 to front *)
        apply Permutation_trans with (l' := -901 :: [300; 7; 289; -277; 300; 5] ++ []).
        { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        
        (* 3. Move -277 to front *)
        apply Permutation_trans with (l' := -277 :: [300; 7; 289] ++ [300; 5]).
        { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        
        (* 4. Move 5 to front *)
        apply Permutation_trans with (l' := 5 :: [300; 7; 289; 300] ++ []).
        { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        
        (* 5. Move 7 to front *)
        apply Permutation_trans with (l' := 7 :: [300] ++ [289; 300]).
        { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        
        (* 6. Move 289 to front *)
        apply Permutation_trans with (l' := 289 :: [300] ++ [300]).
        { apply Permutation_middle. }
        apply Permutation_cons.
        simpl.
        
        apply Permutation_refl.
        
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_cons.
                { apply Sorted_cons.
                  { apply Sorted_cons.
                    { apply Sorted_cons.
                      { apply Sorted_nil. }
                      { simpl. apply HdRel_nil. }
                    }
                    { simpl. apply HdRel_cons. lia. }
                  }
                  { simpl. apply HdRel_cons. lia. }
                }
                { simpl. apply HdRel_cons. lia. }
              }
              { simpl. apply HdRel_cons. lia. }
            }
            { simpl. apply HdRel_cons. lia. }
          }
          { simpl. apply HdRel_cons. lia. }
        }
        { simpl. apply HdRel_cons. lia. }
Qed.