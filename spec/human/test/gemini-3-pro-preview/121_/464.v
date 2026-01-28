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

Example test_case : problem_121_spec [86; 2; 3; 65; 5; 6; 42; 53; 77; 2; 9; 10] 94.
Proof.
  unfold problem_121_spec.
  (* Index 0: 86. Even pos, Even val -> Skip *)
  apply soep_skip. right. reflexivity.
  (* Index 1: 2. Odd pos -> Skip *)
  apply soep_skip. left. reflexivity.
  (* Index 2: 3. Even pos, Odd val -> Match. Need 94 - 3 = 91 *)
  apply soep_match with (s_tail := 91). reflexivity. reflexivity.
  (* Index 3: 65. Odd pos -> Skip *)
  apply soep_skip. left. reflexivity.
  (* Index 4: 5. Even pos, Odd val -> Match. Need 91 - 5 = 86 *)
  apply soep_match with (s_tail := 86). reflexivity. reflexivity.
  (* Index 5: 6. Odd pos -> Skip *)
  apply soep_skip. left. reflexivity.
  (* Index 6: 42. Even pos, Even val -> Skip *)
  apply soep_skip. right. reflexivity.
  (* Index 7: 53. Odd pos -> Skip *)
  apply soep_skip. left. reflexivity.
  (* Index 8: 77. Even pos, Odd val -> Match. Need 86 - 77 = 9 *)
  apply soep_match with (s_tail := 9). reflexivity. reflexivity.
  (* Index 9: 2. Odd pos -> Skip *)
  apply soep_skip. left. reflexivity.
  (* Index 10: 9. Even pos, Odd val -> Match. Need 9 - 9 = 0 *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 11: 10. Odd pos -> Skip *)
  apply soep_skip. left. reflexivity.
  (* Nil *)
  apply soep_nil.
Qed.