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

Example test_sum_odd_in_even_pos : problem_121_spec [2;3;4;4;45;6;9;44;11;10] 65.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* sum_odd_in_even_pos_aux [2;3;4;4;45;6;9;44;11;10] 0
     idx=0 even? true
     h=2 odd? no, so add 0 + sum_odd_in_even_pos_aux [3;4;4;45;6;9;44;11;10] 1
  *)
  (* idx=1 even? no, add 0 + sum_odd_in_even_pos_aux [4;4;45;6;9;44;11;10] 2 *)
  (* idx=2 even? yes, h=4 odd? no, add 0 + ... *)
  (* idx=3 even? no, add 0 + ... *)
  (* idx=4 even? yes, h=45 odd? yes, so 45 + ... *)
  (* idx=5 even? no, add 0 + ... *)
  (* idx=6 even? yes, h=9 odd? yes, so 9 + ... *)
  (* idx=7 even? no, add 0 + ... *)
  (* idx=8 even? yes, h=11 odd? yes, so 11 + ... *)
  (* idx=9 even? no, add 0 + ... *)
  reflexivity.
Qed.