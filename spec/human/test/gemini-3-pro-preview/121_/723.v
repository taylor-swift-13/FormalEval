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

Example test_case : problem_121_spec [0; 1; 2; 3; 10; 4; 5; 6; 7; 8; 1; 2; 2] 13.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 0. Position even, Value even. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: Value 1. Position odd. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: Value 2. Position even, Value even. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 3: Value 3. Position odd. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: Value 10. Position even, Value even. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 5: Value 4. Position odd. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: Value 5. Position even, Value odd. Match. Need 5 + 8 = 13. *)
  apply soep_match with (s_tail := 8). { reflexivity. } { reflexivity. }
  (* Index 7: Value 6. Position odd. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 8: Value 7. Position even, Value odd. Match. Need 7 + 1 = 8. *)
  apply soep_match with (s_tail := 1). { reflexivity. } { reflexivity. }
  (* Index 9: Value 8. Position odd. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 10: Value 1. Position even, Value odd. Match. Need 1 + 0 = 1. *)
  apply soep_match with (s_tail := 0). { reflexivity. } { reflexivity. }
  (* Index 11: Value 2. Position odd. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 12: Value 2. Position even, Value even. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Nil *)
  apply soep_nil.
Qed.