Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_odd_in_even_pos_aux (l : list nat) (idx : nat) : nat :=
  match l with
  | [] => 0
  | h::t => (if (Nat.even idx) && negb (Nat.even h) then h else 0) + sum_odd_in_even_pos_aux t (S idx)
  end.

Definition sum_odd_in_even_pos_impl (l : list nat) : nat := sum_odd_in_even_pos_aux l 0.

Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  output = sum_odd_in_even_pos_impl l.

Example test_sum_odd_in_even_pos : problem_121_spec [31;43;53;75;97;120;75] 256.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* sum_odd_in_even_pos_aux [31;43;53;75;97;120;75] 0
     idx=0 even? true, h=31 odd? yes, add 31 +
  sum_odd_in_even_pos_aux [43;53;75;97;120;75] 1
     idx=1 even? false, add 0 +
  sum_odd_in_even_pos_aux [53;75;97;120;75] 2
     idx=2 even? true, h=53 odd? yes, add 53 +
  sum_odd_in_even_pos_aux [75;97;120;75] 3
     idx=3 even? false, add 0 +
  sum_odd_in_even_pos_aux [97;120;75] 4
     idx=4 even? true, h=97 odd? yes, add 97 +
  sum_odd_in_even_pos_aux [120;75] 5
     idx=5 even? false, add 0 +
  sum_odd_in_even_pos_aux [75] 6
     idx=6 even? true, h=75 odd? yes, add 75 +
  sum_odd_in_even_pos_aux [] 7 = 0
  total: 31 + 0 + 53 + 0 + 97 + 0 + 75 = 256
  *)
  reflexivity.
Qed.