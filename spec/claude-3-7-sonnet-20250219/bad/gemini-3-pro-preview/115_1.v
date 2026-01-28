Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition sum_list (l : list nat) : nat :=
  fold_left Nat.add l 0.

Definition ceil_div (n d : nat) : nat :=
  (n + d - 1) / d.

Definition max_fill_spec (grid : list (list nat)) (capacity : nat) (ans : nat) : Prop :=
  (forall row, In row grid -> 
     forall x, In x row -> (x = 0 \/ x = 1)) /\
  capacity >= 1 /\ capacity <= 10 /\
  (length grid >= 1 /\ length grid <= 100) /\
  (forall r1 r2, In r1 grid -> In r2 grid -> length r1 = length r2) /\
  (forall row, In row grid -> length row >= 1 /\ length row <= 100) /\
  ans = fold_left (fun acc row => acc + ceil_div (sum_list row) capacity) grid 0.

Example test_max_fill : max_fill_spec [[0; 0; 1; 0]; [0; 1; 0; 0]; [1; 1; 1; 1]] 1 6.
Proof.
  unfold max_fill_spec.
  repeat split.
  - (* Check that all elements are 0 or 1 *)
    intros r Hr x Hx.
    simpl in Hr.
    repeat destruct Hr as [H | Hr]; subst; simpl in Hx;
    repeat destruct Hx as [H | Hx]; subst; auto; try contradiction.
  - (* Capacity >= 1 *)
    lia.
  - (* Capacity <= 10 *)
    lia.
  - (* Grid length >= 1 *)
    simpl; lia.
  - (* Grid length <= 100 *)
    simpl; lia.
  - (* All rows have same length *)
    intros r1 r2 H1 H2.
    simpl in H1; simpl in H2.
    repeat destruct H1 as [H1 | H1]; repeat destruct H2 as [H2 | H2];
    try contradiction; subst; reflexivity.
  - (* Row length bounds *)
    intros r Hr.
    simpl in Hr.
    repeat destruct Hr as [H | Hr]; try contradiction; subst; simpl; split; lia.
  - (* Calculation of ans *)
    reflexivity.
Qed.