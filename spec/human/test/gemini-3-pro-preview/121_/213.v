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

Example test_case : problem_121_spec [56; 11; 3; 4; 5; 88; 9; 8; 55; 11; 10; 8; 8] 72.
Proof.
  unfold problem_121_spec.
  (* Index 0: 56. Even index, even value. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: 11. Odd index. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: 3. Even index, odd value. Match. 3 + 69 = 72. *)
  apply soep_match with (s_tail := 69). { reflexivity. } { reflexivity. }
  (* Index 3: 4. Odd index. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: 5. Even index, odd value. Match. 5 + 64 = 69. *)
  apply soep_match with (s_tail := 64). { reflexivity. } { reflexivity. }
  (* Index 5: 88. Odd index. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: 9. Even index, odd value. Match. 9 + 55 = 64. *)
  apply soep_match with (s_tail := 55). { reflexivity. } { reflexivity. }
  (* Index 7: 8. Odd index. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 8: 55. Even index, odd value. Match. 55 + 0 = 55. *)
  apply soep_match with (s_tail := 0). { reflexivity. } { reflexivity. }
  (* Index 9: 11. Odd index. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 10: 10. Even index, even value. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 11: 8. Odd index. Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 12: 8. Even index, even value. Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 13: Nil. Base case. *)
  apply soep_nil.
Qed.