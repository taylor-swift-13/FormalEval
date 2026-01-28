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

Example test_sum_odd_in_even_pos : problem_121_spec [76; 22; 33; 100; 44; 65; 55; 66; 88; 99; 0; 22; 33; 88] 121.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? yes, h=76 even? no add 0 *)
  (* idx=1 odd, add 0 *)
  (* idx=2 even? yes, h=33 odd? yes add 33 *)
  (* idx=3 odd, add 0 *)
  (* idx=4 even? yes, h=44 even? yes add 0 *)
  (* idx=5 odd, add 0 *)
  (* idx=6 even? yes, h=55 odd? yes add 55 *)
  (* idx=7 odd, add 0 *)
  (* idx=8 even? yes, h=88 even? yes add 0 *)
  (* idx=9 odd, add 0 *)
  (* idx=10 even? yes, h=0 even? yes add 0 *)
  (* idx=11 odd, add 0 *)
  (* idx=12 even? yes, h=33 odd? yes add 33 *)
  (* idx=13 odd, add 0 *)
  reflexivity.
Qed.