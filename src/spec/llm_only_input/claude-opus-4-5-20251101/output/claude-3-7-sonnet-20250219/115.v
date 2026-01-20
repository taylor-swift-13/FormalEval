Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Div2.
Require Import Coq.Init.Nat.
Require Import Lia.

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

Example max_fill_test : 
  max_fill_spec [[0; 0; 1; 0]; [0; 1; 0; 0]; [1; 1; 1; 1]] 1 6.
Proof.
  unfold max_fill_spec.
  split.
  - (* All elements are 0 or 1 *)
    intros r Hr x Hx.
    simpl in Hr.
    destruct Hr as [H | [H | [H | H]]]; try contradiction;
    subst r; simpl in Hx;
    destruct Hx as [H | [H | [H | [H | H]]]]; try contradiction;
    subst x; (left; reflexivity) || (right; reflexivity).
  - split.
    + (* capacity >= 1 *)
      lia.
    + split.
      * (* capacity <= 10 *)
        lia.
      * split.
        -- (* length grid >= 1 /\ length grid <= 100 *)
           simpl. lia.
        -- split.
           ++ (* all rows have same length *)
              intros r1 r2 Hr1 Hr2.
              simpl in Hr1, Hr2.
              destruct Hr1 as [H1 | [H1 | [H1 | H1]]]; try contradiction;
              destruct Hr2 as [H2 | [H2 | [H2 | H2]]]; try contradiction;
              subst r1 r2; reflexivity.
           ++ split.
              ** (* all rows have length >= 1 and <= 100 *)
                 intros r Hr.
                 simpl in Hr.
                 destruct Hr as [H | [H | [H | H]]]; try contradiction;
                 subst r; simpl; lia.
              ** (* ans = fold_left ... *)
                 unfold sum_list, ceil_div.
                 simpl.
                 reflexivity.
Qed.