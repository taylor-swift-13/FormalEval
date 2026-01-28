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

Example test_sum_odd_in_even_pos : problem_121_spec [2;3;4;5;88;6;9;8;11;10;86] 20.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even=true, h=2 even => condition false, add 0 + sum_odd_in_even_pos_aux [3;4;5;88;6;9;8;11;10;86] 1 *)
  (* idx=1 even=false, add 0 + sum at idx=2 *)
  (* idx=2 even=true, h=4 even => false, add 0 + sum at idx=3 *)
  (* idx=3 even=false, add 0 + sum at idx=4 *)
  (* idx=4 even=true, h=88 even => false, add 0 + sum at idx=5 *)
  (* idx=5 even=false, add 0 + sum at idx=6 *)
  (* idx=6 even=true, h=9 odd => add 9 + sum at idx=7 *)
  (* idx=7 even=false, add 0 + sum at idx=8 *)
  (* idx=8 even=true, h=11 odd => add 11 + sum at idx=9 *)
  (* idx=9 even=false, add 0 + sum at idx=10 *)
  (* idx=10 even=true, h=86 even => false, add 0 + sum at idx=11 *)
  reflexivity.
Qed.