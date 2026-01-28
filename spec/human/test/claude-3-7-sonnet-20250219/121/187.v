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

Example test_sum_odd_in_even_pos : problem_121_spec [11;22;33;44;65;55;66;88;99;22;22] 208.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* index 0 even, 11 odd -> 11 *)
  (* index 1 odd, skip *)
  (* index 2 even, 33 odd -> 33 *)
  (* index 3 odd, skip *)
  (* index 4 even, 65 odd -> 65 *)
  (* index 5 odd, skip *)
  (* index 6 even, 66 even -> skip *)
  (* index 7 odd, skip *)
  (* index 8 even, 99 odd -> 99 *)
  (* index 9 odd, skip *)
  (* index 10 even, 22 even -> skip *)
  reflexivity.
Qed.