Require Import List.
Require Import Sorting.
Require Import Permutation.
Require Import Arith.
Require Import Lia.

Import ListNotations.

Definition is_sorted (l : list nat) : Prop :=
  forall i j, i < j -> j < length l -> 
    nth i l 0 <= nth j l 0.

Definition no_duplicates (l : list nat) : Prop :=
  NoDup l.

Definition all_elements_from (result original : list nat) : Prop :=
  forall x, In x result <-> In x original.

Definition unique_spec (l : list nat) (result : list nat) : Prop :=
  is_sorted result /\
  no_duplicates result /\
  all_elements_from result l.

Example test_unique_sort : 
  unique_spec [5; 3; 5; 2; 3; 3; 9; 0; 123] [0; 2; 3; 5; 9; 123].
Proof.
  unfold unique_spec.
  split; [| split].

  (* 1. Proof of is_sorted *)
  - unfold is_sorted.
    intros i j Hij Hlen.
    simpl in Hlen.
    (* Enumerate possible values for i and j given the length constraint *)
    assert (Hi: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia.
    assert (Hj: j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
    destruct Hi as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    destruct Hj as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    try lia. (* Discard cases where i < j does not hold *)
    all: simpl; lia. (* Verify values *)

  (* 2. Proof of no_duplicates *)
  - unfold no_duplicates.
    repeat constructor.
    all: simpl; intro H; repeat (destruct H as [H | H]; [try lia | ]); try contradiction.

  (* 3. Proof of all_elements_from *)
  - unfold all_elements_from.
    intro x.
    split; intro H.
    (* Forward: In x result -> In x input *)
    + simpl in H.
      destruct H as [H | [H | [H | [H | [H | [H | H]]]]]]; 
        try contradiction; subst; simpl; tauto.
    (* Backward: In x input -> In x result *)
    + simpl in H.
      destruct H as [H | [H | [H | [H | [H | [H | [H | [H | [H | H]]]]]]]]]; 
        try contradiction; subst; simpl; tauto.
Qed.