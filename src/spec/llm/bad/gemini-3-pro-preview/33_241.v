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

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 105; 4; 5; 700; 900; -200; -901; 800; 1000; 6]
  [-901; 500; 6; 6; 8; 289; 7; -105; -277; 20; 200; 3; 104; 4; 5; 105; 900; -200; 300; 800; 1000; 700].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      destruct (le_lt_dec 22 i) as [Hle | Hlt].
      * assert (Hlen1: length [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 105; 4; 5; 700; 900; -200; -901; 800; 1000; 6] = 22) by reflexivity.
        assert (Hlen2: length [-901; 500; 6; 6; 8; 289; 7; -105; -277; 20; 200; 3; 104; 4; 5; 105; 900; -200; 300; 800; 1000; 700] = 22) by reflexivity.
        assert (H1: nth_error [-901; 500; 6; 6; 8; 289; 7; -105; -277; 20; 200; 3; 104; 4; 5; 105; 900; -200; 300; 800; 1000; 700] i = None).
        { rewrite nth_error_None. rewrite Hlen2. exact Hle. }
        assert (H2: nth_error [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 105; 4; 5; 700; 900; -200; -901; 800; 1000; 6] i = None).
        { rewrite nth_error_None. rewrite Hlen1. exact Hle. }
        rewrite H1, H2. reflexivity.
      * do 22 (destruct i as [|i]; [ 
          try (compute in H; contradiction);
          reflexivity
        | ]).
        exfalso. apply (Nat.le_not_lt 22 (22 + i)). apply Nat.le_add_l. exact Hlt.
    + split.
      * simpl.
        apply Permutation_NoDup.
        -- repeat (constructor; [ simpl; tauto | ]). apply NoDup_nil.
        -- repeat (constructor; [ simpl; tauto | ]). apply NoDup_nil.
        -- intros x. simpl. tauto.
      * simpl.
        repeat (apply Sorted_cons; [ constructor; try (apply Z.leb_le; reflexivity) | ]).
        apply Sorted_nil.
Qed.