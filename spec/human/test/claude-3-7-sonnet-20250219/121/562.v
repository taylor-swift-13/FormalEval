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

Example test_sum_odd_in_even_pos : problem_121_spec [65; 22; 33; 55; 66; 77; 88; 65] 98.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=65 odd? yes, so 65 + sum_odd_in_even_pos_aux tail with idx=1 *)
  (* idx=1 even? false, add 0 + sum from tail *)
  (* idx=2 even? true, h=33 odd? yes, so 33 + sum from tail *)
  (* idx=3 even? false, add 0 + sum from tail *)
  (* idx=4 even? true, h=66 odd? no (even), add 0 + sum *)
  (* idx=5 even? false, add 0 + sum *)
  (* idx=6 even? true, h=88 odd? no (even), add 0 + sum *)
  (* idx=7 even? false, add 0 *)
  reflexivity.
Qed.