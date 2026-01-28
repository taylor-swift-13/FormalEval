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

Example test_case : problem_121_spec [4; 4; 77; 4; 6; 9; 12; 8; 11; 33; 8; 33; 9; 11] 97.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 4 (Even), Position 0 (Even). Skip (Right). *)
  apply soep_skip. right; reflexivity.
  (* Index 1: Value 4, Position 1 (Odd). Skip (Left). *)
  apply soep_skip. left; reflexivity.
  (* Index 2: Value 77 (Odd), Position 2 (Even). Match. Tail sum = 97 - 77 = 20. *)
  apply soep_match with (s_tail := 20). reflexivity. reflexivity.
  (* Index 3: Value 4, Position 3 (Odd). Skip (Left). *)
  apply soep_skip. left; reflexivity.
  (* Index 4: Value 6 (Even), Position 4 (Even). Skip (Right). *)
  apply soep_skip. right; reflexivity.
  (* Index 5: Value 9, Position 5 (Odd). Skip (Left). *)
  apply soep_skip. left; reflexivity.
  (* Index 6: Value 12 (Even), Position 6 (Even). Skip (Right). *)
  apply soep_skip. right; reflexivity.
  (* Index 7: Value 8, Position 7 (Odd). Skip (Left). *)
  apply soep_skip. left; reflexivity.
  (* Index 8: Value 11 (Odd), Position 8 (Even). Match. Tail sum = 20 - 11 = 9. *)
  apply soep_match with (s_tail := 9). reflexivity. reflexivity.
  (* Index 9: Value 33, Position 9 (Odd). Skip (Left). *)
  apply soep_skip. left; reflexivity.
  (* Index 10: Value 8 (Even), Position 10 (Even). Skip (Right). *)
  apply soep_skip. right; reflexivity.
  (* Index 11: Value 33, Position 11 (Odd). Skip (Left). *)
  apply soep_skip. left; reflexivity.
  (* Index 12: Value 9 (Odd), Position 12 (Even). Match. Tail sum = 9 - 9 = 0. *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 13: Value 11, Position 13 (Odd). Skip (Left). *)
  apply soep_skip. left; reflexivity.
  (* End of list *)
  apply soep_nil.
Qed.