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

Example test_case : problem_121_spec [42; 96; 53; 97; 120; 75; 75; 120] 128.
Proof.
  unfold problem_121_spec.
  (* Index 0: 42. Even pos (0), Even val (42). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 1: 96. Odd pos (1). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 2: 53. Even pos (2), Odd val (53). Match. 53 + 75 = 128. *)
  apply soep_match with (s_tail := 75). { reflexivity. } { reflexivity. }
  (* Index 3: 97. Odd pos (3). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 4: 120. Even pos (4), Even val (120). Skip. *)
  apply soep_skip. { right. reflexivity. }
  (* Index 5: 75. Odd pos (5). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 6: 75. Even pos (6), Odd val (75). Match. 75 + 0 = 75. *)
  apply soep_match with (s_tail := 0). { reflexivity. } { reflexivity. }
  (* Index 7: 120. Odd pos (7). Skip. *)
  apply soep_skip. { left. reflexivity. }
  (* Index 8: Nil. *)
  apply soep_nil.
Qed.