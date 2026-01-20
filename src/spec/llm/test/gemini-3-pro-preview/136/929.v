Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition largest_smallest_integers_spec (lst : list Z) (result : option Z * option Z) : Prop :=
  let (neg_res, pos_res) := result in
  (* Specification for the largest negative integer *)
  (match neg_res with
   | Some max_neg => 
       In max_neg lst /\ 
       max_neg < 0 /\ 
       (forall x, In x lst -> x < 0 -> x <= max_neg)
   | None => 
       forall x, In x lst -> x >= 0
   end) /\
  (* Specification for the smallest positive integer *)
  (match pos_res with
   | Some min_pos => 
       In min_pos lst /\ 
       min_pos > 0 /\ 
       (forall x, In x lst -> x > 0 -> min_pos <= x)
   | None => 
       forall x, In x lst -> x <= 0
   end).

Example test_largest_smallest_integers : 
  largest_smallest_integers_spec [0; 0; -4; -1; 2; 1; 2; -2; 0; 0; 2] (Some (-1), Some 1).
Proof.
  unfold largest_smallest_integers_spec.
  split.
  - (* Proving the specification for the negative part (Some -1) *)
    split.
    + (* 1. Prove that -1 is in the list *)
      simpl.
      do 3 right. left. reflexivity.
    + split.
      * (* 2. Prove that -1 < 0 *)
        lia.
      * (* 3. Prove that -1 is greater than or equal to any negative element in the list *)
        intros x H_in H_neg.
        simpl in H_in.
        repeat destruct H_in as [H_eq | H_in]; subst; try lia.
  
  - (* Proving the specification for the positive part (Some 1) *)
    split.
    + (* 1. Prove that 1 is in the list *)
      simpl.
      do 5 right. left. reflexivity.
    + split.
      * (* 2. Prove that 1 > 0 *)
        lia.
      * (* 3. Prove that 1 is less than or equal to any positive element in the list *)
        intros x H_in H_pos.
        simpl in H_in.
        repeat destruct H_in as [H_eq | H_in]; subst; try lia.
Qed.