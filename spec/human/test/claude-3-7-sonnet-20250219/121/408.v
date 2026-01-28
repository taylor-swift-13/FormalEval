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

Example test_sum_odd_in_even_pos : problem_121_spec [11; 33; 44; 55; 66; 88; 99; 0; 22; 33; 88] 110.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* sum_odd_in_even_pos_aux [11;33;44;55;66;88;99;0;22;33;88] 0 *)
  (* idx=0 even? true, h=11 odd? yes → 11 + ... *)
  (* idx=1 even? false → 0 + ... *)
  (* idx=2 even? true, h=44 even? no → 0 + ... *)
  (* idx=3 even? false → 0 + ... *)
  (* idx=4 even? true, h=66 even? no → 0 + ... *)
  (* idx=5 even? false → 0 + ... *)
  (* idx=6 even? true, h=99 odd? yes → 99 + ... *)
  (* idx=7 even? false → 0 + ... *)
  (* idx=8 even? true, h=22 even? no → 0 + ... *)
  (* idx=9 even? false → 0 + ... *)
  (* idx=10 even? true, h=88 even? no → 0 + ... *)
  (* sum = 11 + 0 + 0 + 0 + 0 + 0 + 99 + 0 + 0 + 0 + 0 = 110 *)
  reflexivity.
Qed.