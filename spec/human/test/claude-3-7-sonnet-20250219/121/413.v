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

Example test_sum_odd_in_even_pos : problem_121_spec [3; 3; 3; 4; 6; 9; 12; 8; 12; 10; 8; 9; 11] 17.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? yes; h=3 odd? yes => 3 + ... *)
  (* idx=1 even? no; add 0 + ... *)
  (* idx=2 even? yes; h=3 odd? yes => 3 + ... *)
  (* idx=3 even? no; add 0 + ... *)
  (* idx=4 even? yes; h=6 even? yes => add 0 + ... *)
  (* idx=5 even? no; add 0 + ... *)
  (* idx=6 even? yes; h=12 even? yes => add 0 + ... *)
  (* idx=7 even? no; add 0 + ... *)
  (* idx=8 even? yes; h=12 even? yes => add 0 + ... *)
  (* idx=9 even? no; add 0 + ... *)
  (* idx=10 even? yes; h=8 even? yes => add 0 + ... *)
  (* idx=11 even? no; add 0 + ... *)
  (* idx=12 even? yes; h=11 odd? yes => 11 + ... *)
  (* Sum is 3 + 3 + 11 = 17 *)
  reflexivity.
Qed.