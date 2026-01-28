Existing Coq output file content 
specification for the first test case `input = [[1%Z; 2%Z; 3%Z]], output = [1%Z; 2%Z; 3%Z]`:
```coq
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 0; 5; 700; -104; -200; -104; -901; 800; 1000]
  [-104; 500; 6; 4; 8; 289; 7; -105; -277; 20; 200; 3; 104; 0; 5; 300; -104; -200; 700; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check for i = 0..21. For i >= 22 both are None. *)
      do 22 (destruct i; [
        simpl in H; 
        (* If i mod 3 == 0, H is false (0 <> 0), so we use congruence to solve it. *)
        try (exfalso; compute in H; congruence);
        (* If i mod 3 <> 0, we check equality of elements *)
        simpl; reflexivity 
      | ]).
      (* For i >= 22 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Simplify to concrete lists first *)
        simpl.
        (* Use NoDup_Permutation since elements are unique *)
        apply NoDup_Permutation.
        -- (* NoDup l1 *)
           repeat (constructor; [ intro Hin; simpl in Hin; repeat destruct Hin; try discriminate | ]).
           apply NoDup_nil.
        -- (* NoDup l2 *)
           repeat (constructor; [ intro Hin; simpl in Hin; repeat destruct Hin; try discriminate | ]).
           apply NoDup_nil.
        -- (* Equivalence of In *)
           intros x. simpl. split; intro Hin.
           ++ repeat (destruct Hin as [Hin|Hin]; [ rewrite Hin; repeat (left; reflexivity || right); try contradiction | ]); try contradiction.
           ++ repeat (destruct Hin as [Hin|Hin]; [ rewrite Hin; repeat (left; reflexivity || right); try contradiction | ]); try contradiction.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; apply HdRel_cons; compute; congruence ]).
        apply Sorted_nil.
Qed.