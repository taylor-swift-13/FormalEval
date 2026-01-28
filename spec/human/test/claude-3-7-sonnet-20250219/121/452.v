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

Example test_sum_odd_in_even_pos : problem_121_spec [12;11;22;33;6;65;55;98;66;89;88;22;23;65;88;88] 78.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? true, h=12 even, so add 0 *)
  (* idx=1 even? false, add 0 *)
  (* idx=2 even? true, h=22 even, add 0 *)
  (* idx=3 even? false, add 0 *)
  (* idx=4 even? true, h=6 even, add 0 *)
  (* idx=5 even? false, add 0 *)
  (* idx=6 even? true, h=55 odd, add 55 + ... *)
  (* idx=7 even? false, add 0 *)
  (* idx=8 even? true, h=66 even, add 0 *)
  (* idx=9 even? false, add 0 *)
  (* idx=10 even? true, h=88 even, add 0 *)
  (* idx=11 even? false, add 0 *)
  (* idx=12 even? true, h=23 odd, add 23 + ... *)
  (* idx=13 even? false, add 0 *)
  (* idx=14 even? true, h=88 even, add 0 *)
  (* idx=15 even? false, add 0 *)
  (* sum is 55 + 23 = 78 *)
  reflexivity.
Qed.