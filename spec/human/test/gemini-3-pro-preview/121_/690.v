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

Example test_case : problem_121_spec [31; 42; 87; 53; 75; 86; 97; 120; 75; 75] 365.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31, Even index, Odd value -> Match. 365 = 31 + 334 *)
  apply soep_match with (s_tail := 334); [reflexivity | reflexivity |].
  (* Index 1: 42, Odd index -> Skip *)
  apply soep_skip; [left; reflexivity |].
  (* Index 2: 87, Even index, Odd value -> Match. 334 = 87 + 247 *)
  apply soep_match with (s_tail := 247); [reflexivity | reflexivity |].
  (* Index 3: 53, Odd index -> Skip *)
  apply soep_skip; [left; reflexivity |].
  (* Index 4: 75, Even index, Odd value -> Match. 247 = 75 + 172 *)
  apply soep_match with (s_tail := 172); [reflexivity | reflexivity |].
  (* Index 5: 86, Odd index -> Skip *)
  apply soep_skip; [left; reflexivity |].
  (* Index 6: 97, Even index, Odd value -> Match. 172 = 97 + 75 *)
  apply soep_match with (s_tail := 75); [reflexivity | reflexivity |].
  (* Index 7: 120, Odd index -> Skip *)
  apply soep_skip; [left; reflexivity |].
  (* Index 8: 75, Even index, Odd value -> Match. 75 = 75 + 0 *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity |].
  (* Index 9: 75, Odd index -> Skip *)
  apply soep_skip; [left; reflexivity |].
  apply soep_nil.
Qed.