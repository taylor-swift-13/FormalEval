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

Example test_case : problem_121_spec [31; 120; 42; 53; 75; 86; 97; 52; 119; 75; 75; 120; 53] 450.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31 (Odd), Pos 0 (Even). Match. 450 - 31 = 419 *)
  apply soep_match with (s_tail := 419); [reflexivity | reflexivity | ].
  (* Index 1: 120, Pos 1 (Odd). Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 2: 42 (Even), Pos 2 (Even). Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 3: 53, Pos 3 (Odd). Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 4: 75 (Odd), Pos 4 (Even). Match. 419 - 75 = 344 *)
  apply soep_match with (s_tail := 344); [reflexivity | reflexivity | ].
  (* Index 5: 86, Pos 5 (Odd). Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 6: 97 (Odd), Pos 6 (Even). Match. 344 - 97 = 247 *)
  apply soep_match with (s_tail := 247); [reflexivity | reflexivity | ].
  (* Index 7: 52, Pos 7 (Odd). Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 8: 119 (Odd), Pos 8 (Even). Match. 247 - 119 = 128 *)
  apply soep_match with (s_tail := 128); [reflexivity | reflexivity | ].
  (* Index 9: 75, Pos 9 (Odd). Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 10: 75 (Odd), Pos 10 (Even). Match. 128 - 75 = 53 *)
  apply soep_match with (s_tail := 53); [reflexivity | reflexivity | ].
  (* Index 11: 120, Pos 11 (Odd). Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 12: 53 (Odd), Pos 12 (Even). Match. 53 - 53 = 0 *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity | ].
  (* End of list *)
  apply soep_nil.
Qed.