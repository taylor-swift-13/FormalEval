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

Example test_case : problem_121_spec [2; 4; 5; 6; 7; 8; 9; 31; 10] 21.
Proof.
  unfold problem_121_spec.
  (* Index 0: 2. Even pos, Even val. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: 4. Odd pos. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: 5. Even pos, Odd val. Match. 5 + 16 = 21. *)
  apply soep_match with (s_tail := 16). { reflexivity. } { reflexivity. }
  (* Index 3: 6. Odd pos. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: 7. Even pos, Odd val. Match. 7 + 9 = 16. *)
  apply soep_match with (s_tail := 9). { reflexivity. } { reflexivity. }
  (* Index 5: 8. Odd pos. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: 9. Even pos, Odd val. Match. 9 + 0 = 9. *)
  apply soep_match with (s_tail := 0). { reflexivity. } { reflexivity. }
  (* Index 7: 31. Odd pos. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 8: 10. Even pos, Even val. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 9: Nil. *)
  apply soep_nil.
Qed.