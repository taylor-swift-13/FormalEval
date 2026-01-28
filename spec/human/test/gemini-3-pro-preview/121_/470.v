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

Example test_case : problem_121_spec [2; 5; 2; 2; 33; 1; 5; 5; 5; 42; 1; 1; 5; 5] 49.
Proof.
  unfold problem_121_spec.
  (* Index 0: 2. Even pos, Even val -> Skip *)
  apply soep_skip. right; reflexivity.
  (* Index 1: 5. Odd pos -> Skip *)
  apply soep_skip. left; reflexivity.
  (* Index 2: 2. Even pos, Even val -> Skip *)
  apply soep_skip. right; reflexivity.
  (* Index 3: 2. Odd pos -> Skip *)
  apply soep_skip. left; reflexivity.
  (* Index 4: 33. Even pos, Odd val -> Match. Remaining sum 16 *)
  apply soep_match with (s_tail := 16). reflexivity. reflexivity.
  (* Index 5: 1. Odd pos -> Skip *)
  apply soep_skip. left; reflexivity.
  (* Index 6: 5. Even pos, Odd val -> Match. Remaining sum 11 *)
  apply soep_match with (s_tail := 11). reflexivity. reflexivity.
  (* Index 7: 5. Odd pos -> Skip *)
  apply soep_skip. left; reflexivity.
  (* Index 8: 5. Even pos, Odd val -> Match. Remaining sum 6 *)
  apply soep_match with (s_tail := 6). reflexivity. reflexivity.
  (* Index 9: 42. Odd pos -> Skip *)
  apply soep_skip. left; reflexivity.
  (* Index 10: 1. Even pos, Odd val -> Match. Remaining sum 5 *)
  apply soep_match with (s_tail := 5). reflexivity. reflexivity.
  (* Index 11: 1. Odd pos -> Skip *)
  apply soep_skip. left; reflexivity.
  (* Index 12: 5. Even pos, Odd val -> Match. Remaining sum 0 *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 13: 5. Odd pos -> Skip *)
  apply soep_skip. left; reflexivity.
  (* Index 14: Nil *)
  apply soep_nil.
Qed.