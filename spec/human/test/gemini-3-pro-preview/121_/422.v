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

Example test_case : problem_121_spec [55; 0; 1; 2; 3; 4; 4; 5; 6; 7; 8; 9; 10; 4; 9] 68.
Proof.
  unfold problem_121_spec.
  (* Index 0: 55. Even pos, Odd val. Match. 55 + 13 = 68 *)
  apply soep_match with (s_tail := 13). reflexivity. reflexivity.
  (* Index 1: 0. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 2: 1. Even pos, Odd val. Match. 1 + 12 = 13 *)
  apply soep_match with (s_tail := 12). reflexivity. reflexivity.
  (* Index 3: 2. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 4: 3. Even pos, Odd val. Match. 3 + 9 = 12 *)
  apply soep_match with (s_tail := 9). reflexivity. reflexivity.
  (* Index 5: 4. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 6: 4. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 7: 5. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 8: 6. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 9: 7. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 10: 8. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 11: 9. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 12: 10. Even pos, Even val. Skip. *)
  apply soep_skip. right. reflexivity.
  (* Index 13: 4. Odd pos. Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 14: 9. Even pos, Odd val. Match. 9 + 0 = 9 *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 15: Nil. *)
  apply soep_nil.
Qed.