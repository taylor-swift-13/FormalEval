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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; 18; -8; 1001; -901; 800; 1000; 0; -277; -8; 300]
  [-8; 500; 6; 0; 8; 289; 7; -105; -277; 20; 200; 3; 104; 5; 700; 300; 18; -8; 900; -901; 800; 1000; 0; -277; 1001; 300].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      repeat (destruct i; [ simpl in H; try (exfalso; apply H; reflexivity); simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat (apply NoDup_cons; [ simpl; intuition discriminate | ]).
           apply NoDup_nil.
        -- repeat (apply NoDup_cons; [ simpl; intuition discriminate | ]).
           apply NoDup_nil.
        -- intros x; split; intro H0;
           repeat (destruct H0 as [H0|H0]; [ rewrite <- H0; simpl; auto | ]);
           try contradiction.
      * simpl.
        repeat constructor; try lia.
Qed.