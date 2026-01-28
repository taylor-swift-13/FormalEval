Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Definition largest_smallest_integers_spec (lst : list Z) (a b : option Z) : Prop :=
  (
    (a = None /\ forall n, In n lst -> n < 0 -> False)
    \/
    exists m, a = Some m /\ In m lst /\ m < 0 /\ forall n, In n lst -> n < 0 -> n <= m
  )
  /\
  (
    (b = None /\ forall n, In n lst -> n > 0 -> False)
    \/
    exists p, b = Some p /\ In p lst /\ p > 0 /\ forall n, In n lst -> n > 0 -> p <= n
  ).

Example test_case: largest_smallest_integers_spec [0; 0; -1; 3; -8; 2; 1; -2; 0; 0; 2; 2] (Some (-1)) (Some 1).
Proof.
  unfold largest_smallest_integers_spec.
  split.
  - (* Proving the first part regarding negatives (Some -1) *)
    right.
    exists (-1).
    split.
    + reflexivity.
    + split.
      * (* Proving -1 is in the list *)
        simpl. right. right. left. reflexivity.
      * split.
        -- (* Proving -1 < 0 *)
           lia.
        -- (* Proving -1 is the largest negative *)
           intros n H_in H_neg.
           simpl in H_in.
           destruct H_in as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]; subst; lia.
  - (* Proving the second part regarding positives (Some 1) *)
    right.
    exists 1.
    split.
    + reflexivity.
    + split.
      * (* Proving 1 is in the list *)
        simpl. right. right. right. right. right. right. left. reflexivity.
      * split.
        -- (* Proving 1 > 0 *)
           lia.
        -- (* Proving 1 is the smallest positive *)
           intros n H_in H_pos.
           simpl in H_in.
           destruct H_in as [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]]]; subst; lia.
Qed.