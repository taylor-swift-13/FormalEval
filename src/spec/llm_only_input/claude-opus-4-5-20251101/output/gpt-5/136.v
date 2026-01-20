Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
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

Example test_largest_smallest_integers :
  largest_smallest_integers_spec [2%Z; 4%Z; 1%Z; 3%Z; 5%Z; 7%Z] None (Some 1%Z).
Proof.
  unfold largest_smallest_integers_spec.
  split.
  - (* Part a = None: no negative numbers *)
    left.
    split.
    + reflexivity.
    + intros n Hin Hneg.
      simpl in Hin.
      destruct Hin as [H | [H | [H | [H | [H | [H | H]]]]]];
        subst; lia.
  - (* Part b = Some 1: smallest positive is 1 *)
    right.
    exists 1%Z.
    split; [reflexivity |].
    split.
    + simpl. right. right. left. reflexivity.
    + split.
      * lia.
      * intros n Hin Hpos.
        simpl in Hin.
        destruct Hin as [H | [H | [H | [H | [H | [H | H]]]]]];
          subst; lia.
Qed.