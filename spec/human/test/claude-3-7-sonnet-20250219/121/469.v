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

Example test_sum_odd_in_even_pos : problem_121_spec [11;22;33;100;55;66;77;88;99;66] 275.
Proof.
  unfold problem_121_spec, sum_odd_in_even_pos_impl.
  simpl.
  (* idx=0 even? yes; h=11 odd? yes. add 11 + ... *)
  (* next idx=1 odd, skip *)
  (* idx=2 even; h=33 odd? yes; add 33 + ... *)
  (* idx=3 odd, skip *)
  (* idx=4 even; h=55 odd? yes; add 55 + ... *)
  (* idx=5 odd, skip *)
  (* idx=6 even; h=77 odd? yes; add 77 + ... *)
  (* idx=7 odd, skip *)
  (* idx=8 even; h=99 odd? yes; add 99 + ... *)
  (* idx=9 odd, skip *)
  (* total = 11+33+55+77+99 = 275 *)
  reflexivity.
Qed.