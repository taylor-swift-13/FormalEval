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

Example test_sum_odd_in_even_pos : problem_121_spec [31;120;42;55;53;75;86;52;119;75;75] 278.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=31 odd? yes, add 31 + ... *)
  (* idx=1 even? false, add 0 + ... *)
  (* idx=2 even? true, h=42 even, add 0 + ... *)
  (* idx=3 even? false, add 0 + ... *)
  (* idx=4 even? true, h=53 odd? yes, add 53 + ... *)
  (* idx=5 even? false, add 0 + ... *)
  (* idx=6 even? true, h=86 even, add 0 + ... *)
  (* idx=7 even? false, add 0 + ... *)
  (* idx=8 even? true, h=119 odd? yes, add 119 + ... *)
  (* idx=9 even? false, add 0 + ... *)
  (* idx=10 even? true, h=75 odd? yes, add 75 + ... *)
  reflexivity.
Qed.