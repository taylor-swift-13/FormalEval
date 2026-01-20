Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; -1; 5; 700; 900; -901; 800; 1000; 6; 0; -277]
  [-277; 500; 6; -1; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 300; -901; 800; 900; 6; 0; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length *)
    simpl. reflexivity.
  - split.
    + (* 2. indices *)
      intros i H.
      do 22 (destruct i; [ simpl; try reflexivity; try (simpl in H; try congruence; try lia) | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation *)
        simpl.
        Ltac solve_concrete_perm :=
          repeat match goal with
          | |- Permutation [] [] => apply Permutation_nil
          | |- Permutation (?x :: ?xs) ?ys =>
             let rec split_list l acc :=
               match l with
               | x :: ?tl => constr:((acc, tl))
               | ?h :: ?tl => split_list tl (acc ++ [h])
               end
             in
             let p := split_list ys (@nil Z) in
             match p with
             | (?l1, ?l2) =>
                 apply Permutation_trans with (x :: l1 ++ l2);
                 [ apply Permutation_cons | apply Permutation_middle ]
             end
          end.
        solve_concrete_perm.
      * (* 4. Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.