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

Example test_sum_odd_in_even_pos : problem_121_spec [31; 42; 3; 64; 87; 75; 97; 108; 119] 337.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* index 0 even, 31 odd, add 31 *)
  (* index 1 odd, skip *)
  (* index 2 even, 3 odd, add 3 *)
  (* index 3 odd, skip *)
  (* index 4 even, 87 odd, add 87 *)
  (* index 5 odd, skip *)
  (* index 6 even, 97 odd, add 97 *)
  (* index 7 odd, skip *)
  (* index 8 even, 119 odd, add 119 *)
  reflexivity.
Qed.