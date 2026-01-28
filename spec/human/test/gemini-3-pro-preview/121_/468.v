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

Example test_case : problem_121_spec [2; 5; 2; 2; 33; 1; 1; 5; 5; 5; 42; 1; 1; 5; 5; 1; 2; 1] 45.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 2. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 1: Value 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 2: Value 2. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 3: Value 2. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 4: Value 33. Even pos, Odd val. Match. Need 33 + 12 = 45. *)
  apply soep_match with (s_tail := 12). reflexivity. reflexivity.
  (* Index 5: Value 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 6: Value 1. Even pos, Odd val. Match. Need 1 + 11 = 12. *)
  apply soep_match with (s_tail := 11). reflexivity. reflexivity.
  (* Index 7: Value 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 8: Value 5. Even pos, Odd val. Match. Need 5 + 6 = 11. *)
  apply soep_match with (s_tail := 6). reflexivity. reflexivity.
  (* Index 9: Value 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 10: Value 42. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 11: Value 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 12: Value 1. Even pos, Odd val. Match. Need 1 + 5 = 6. *)
  apply soep_match with (s_tail := 5). reflexivity. reflexivity.
  (* Index 13: Value 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 14: Value 5. Even pos, Odd val. Match. Need 5 + 0 = 5. *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 15: Value 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 16: Value 2. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 17: Value 1. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 18: Nil. Base case. *)
  apply soep_nil.
Qed.