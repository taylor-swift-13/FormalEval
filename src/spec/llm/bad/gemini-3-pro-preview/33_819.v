Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
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

Ltac find_and_bring_to_front x :=
  match goal with
  | |- Permutation ?l _ =>
     let rec split_list lst :=
       match lst with
       | x :: ?tl => constr:((@nil Z, tl))
       | ?y :: ?tl =>
          let res := split_list tl in
          match res with
          | (?pre, ?post) => constr:((y :: pre, post))
          end
       end
     in
     let parts := split_list l in
     match parts with
     | (?pre, ?post) =>
         transitivity (x :: pre ++ post);
         [ | apply Permutation_middle ]
     end
  end.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 4; 4; 5; 700; 900; -200; -104; -901; 800; 1000; 1000]
  [-901; 500; 6; 4; 8; 289; 7; -105; -277; 20; 200; 4; 104; 5; 700; 300; -200; -104; 900; 800; 1000; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i as [|i]; [ 
        simpl in *; 
        try (exfalso; apply H; reflexivity); 
        try reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        repeat match goal with
        | |- Permutation _ (?x :: ?xs) =>
            find_and_bring_to_front x;
            apply Permutation_cons
        | |- Permutation _ [] => apply Permutation_nil
        end.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; constructor; try discriminate]).
        apply Sorted_nil.
Qed.