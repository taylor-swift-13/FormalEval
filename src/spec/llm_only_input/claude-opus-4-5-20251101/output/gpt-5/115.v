Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.

Definition sum_list (l : list nat) : nat := fold_right Nat.add 0 l.

Definition divceil (n c : nat) : nat := Nat.div (n + c - 1) c.

Definition max_fill_spec (grid : list (list nat)) (capacity : nat) (ans : nat) : Prop :=
  ans = fold_right (fun l acc => acc + divceil (sum_list l) capacity) 0 grid.

Example test_max_fill :
  max_fill_spec ((0 :: 0 :: 1 :: 0 :: nil) :: (0 :: 1 :: 0 :: 0 :: nil) :: (1 :: 1 :: 1 :: 1 :: nil) :: nil) 1 6.
Proof.
  unfold max_fill_spec.
  unfold fold_right.
  unfold sum_list.
  unfold divceil.
  simpl.
  reflexivity.
Qed.