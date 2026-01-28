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

Example test_case : problem_121_spec [2; 5; 2; 2; 33; 1; 1; 5; 5; 5; 42; 1; 1; 5; 5] 45.
Proof.
  unfold problem_121_spec.
  (* Index 0: Val 2. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 1: Val 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 2: Val 2. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 3: Val 2. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 4: Val 33. Even pos, Odd val. Match. Tail sum = 12. *)
  apply soep_match with (s_tail := 12). reflexivity. reflexivity.
  (* Index 5: Val 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 6: Val 1. Even pos, Odd val. Match. Tail sum = 11. *)
  apply soep_match with (s_tail := 11). reflexivity. reflexivity.
  (* Index 7: Val 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 8: Val 5. Even pos, Odd val. Match. Tail sum = 6. *)
  apply soep_match with (s_tail := 6). reflexivity. reflexivity.
  (* Index 9: Val 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 10: Val 42. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 11: Val 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 12: Val 1. Even pos, Odd val. Match. Tail sum = 5. *)
  apply soep_match with (s_tail := 5). reflexivity. reflexivity.
  (* Index 13: Val 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 14: Val 5. Even pos, Odd val. Match. Tail sum = 0. *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 15: Nil. *)
  apply soep_nil.
Qed.