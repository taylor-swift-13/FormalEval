Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope R_scope.

Definition find_closest_elements_spec (numbers : list R) (result : R * R) : Prop :=
  let (a, b) := result in
  (length numbers >= 2)%nat ->
  a <= b /\
  (exists i j : nat, i <> j /\ nth_error numbers i = Some a /\ nth_error numbers j = Some b) /\
  (forall i j : nat, forall x y : R,
    i <> j ->
    nth_error numbers i = Some x ->
    nth_error numbers j = Some y ->
    b - a <= Rabs (x - y)).

Example test_find_closest_elements : find_closest_elements_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] (3.9, 4.0).
Proof.
  unfold find_closest_elements_spec.
  intros _.
  split.
  - (* Prove a <= b *)
    lra.
  - split.
    + (* Prove existence of indices i=2, j=3 *)
      exists 2%nat, 3%nat.
      split.
      * lia.
      * split; reflexivity.
    + (* Prove optimality for all pairs *)
      intros i j x y Hneq Hx Hy.
      
      (* Destruct i to enumerate all elements for x *)
      destruct i; [injection Hx as <- |
      destruct i; [injection Hx as <- |
      destruct i; [injection Hx as <- |
      destruct i; [injection Hx as <- |
      destruct i; [injection Hx as <- |
      destruct i; [injection Hx as <- |
      simpl in Hx; discriminate Hx ]]]]]];
      
      (* Destruct j to enumerate all elements for y *)
      destruct j; [injection Hy as <- |
      destruct j; [injection Hy as <- |
      destruct j; [injection Hy as <- |
      destruct j; [injection Hy as <- |
      destruct j; [injection Hy as <- |
      destruct j; [injection Hy as <- |
      simpl in Hy; discriminate Hy ]]]]]].

      (* Case i = j: contradiction with Hneq *)
      all: try (elim Hneq; reflexivity).
      
      (* Case i <> j: verify inequality *)
      all: simpl; lra.
Qed.