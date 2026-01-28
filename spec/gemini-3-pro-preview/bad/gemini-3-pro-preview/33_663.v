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
  [500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 291; 800; 1000; 105; 290] 
  [-901; 6; 7; 4; 8; 289; 20; -105; -277; 104; 200; 3; 290; 700; 900; 500; 291; 800; 1000; 105; 290].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      do 21 (destruct i as [|i]; [ 
        simpl in H; 
        try (elim H; reflexivity); 
        simpl; reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ intro HIn; repeat destruct HIn as [HIn|HIn]; try discriminate HIn | ]). apply NoDup_nil.
        -- repeat (constructor; [ intro HIn; repeat destruct HIn as [HIn|HIn]; try discriminate HIn | ]). apply NoDup_nil.
        -- intros x. split; intro Hx; simpl in Hx; repeat destruct Hx as [Hx|Hx]; subst; simpl; tauto.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; unfold Z.le; simpl; intro C; discriminate C ]).
        apply Sorted_nil.
Qed.