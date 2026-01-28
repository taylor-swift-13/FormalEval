Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0%nat
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

(* 非空整数列表 *)
Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_case : problem_121_spec [65; 10; 22; 33; 44; 55; 76; 66; 77; 88; 22; 33] 142.
Proof.
  unfold problem_121_spec.
  (* i=0: 65 is odd, pos 0 is even. Match. 65 + 77 = 142 *)
  apply soep_match with (s_tail := 77).
  { reflexivity. }
  { reflexivity. }
  (* i=1: pos 1 is odd. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* i=2: 22 is even, pos 2 is even. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* i=3: pos 3 is odd. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* i=4: 44 is even, pos 4 is even. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* i=5: pos 5 is odd. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* i=6: 76 is even, pos 6 is even. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* i=7: pos 7 is odd. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* i=8: 77 is odd, pos 8 is even. Match. 77 + 0 = 77 *)
  apply soep_match with (s_tail := 0).
  { reflexivity. }
  { reflexivity. }
  (* i=9: pos 9 is odd. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* i=10: 22 is even, pos 10 is even. Skip. *)
  apply soep_skip.
  { right. reflexivity. }
  (* i=11: pos 11 is odd. Skip. *)
  apply soep_skip.
  { left. reflexivity. }
  (* i=12: nil. *)
  apply soep_nil.
Qed.