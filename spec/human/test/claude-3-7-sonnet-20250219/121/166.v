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

Example test_sum_odd_in_even_pos : problem_121_spec [11;22;33;56;44;65;55;66;88;99;22;22] 99.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even, h=11 odd, add 11 *)
  (* idx=1 odd index, add 0 *)
  (* idx=2 even, h=33 odd, add 33 *)
  (* idx=3 odd, add 0 *)
  (* idx=4 even, h=44 even, add 0 *)
  (* idx=5 odd, add 0 *)
  (* idx=6 even, h=55 odd, add 55 *)
  (* idx=7 odd, add 0 *)
  (* idx=8 even, h=88 even, add 0 *)
  (* idx=9 odd, add 0 *)
  (* idx=10 even, h=22 even, add 0 *)
  (* idx=11 odd, add 0 *)
  (* Sum: 11 + 33 + 55 = 99 *)
  reflexivity.
Qed.