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

Example test_sum_odd_in_even_pos : problem_121_spec [0; 1; 1; 1; 1; 1; 97; 1; 1; 0; 1] 101.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=0 even? yes, so 0 *)
  (* idx=1 even? false, 0 + sum tail *)
  (* idx=2 even? true, h=1 odd? yes, so 1 + ... *)
  (* idx=3 even? false *)
  (* idx=4 even? true, h=1 odd? yes, +1 *)
  (* idx=5 false *)
  (* idx=6 true, h=97 odd? yes, +97 *)
  (* idx=7 false *)
  (* idx=8 true, h=1 odd? yes, +1 *)
  (* idx=9 false *)
  (* idx=10 true, h=1 odd? yes, +1 *)
  reflexivity.
Qed.