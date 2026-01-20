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
  [300; 500; 6; 7; 8; 289; 21; -105; -277; 104; 200; 4; 5; 700; 900; -200; -901; 800; 1000] 
  [-200; 500; 6; 5; 8; 289; 7; -105; -277; 21; 200; 4; 104; 700; 900; 300; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [
        simpl; 
        try reflexivity; 
        try (exfalso; compute in H; congruence)
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat constructor; simpl; try (intro H1; repeat (destruct H1 as [H1|H1]; [ try discriminate | ]); tauto).
        -- repeat constructor; simpl; try (intro H1; repeat (destruct H1 as [H1|H1]; [ try discriminate | ]); tauto).
        -- intros x. split; intro Hx;
           simpl in *;
           repeat (destruct Hx as [Hx | Hx]; [ subst; simpl; tauto | ]);
           tauto.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.