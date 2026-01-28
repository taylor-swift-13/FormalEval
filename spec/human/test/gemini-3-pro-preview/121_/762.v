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

Example test_case : problem_121_spec [31; 42; 3; 64; 87; 75; 97; 108; 119] 337.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31 (Odd), Pos 0 (Even). Match. Tail sum = 337 - 31 = 306 *)
  apply soep_match with (s_tail := 306). reflexivity. reflexivity.
  (* Index 1: 42, Pos 1 (Odd). Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 2: 3 (Odd), Pos 2 (Even). Match. Tail sum = 306 - 3 = 303 *)
  apply soep_match with (s_tail := 303). reflexivity. reflexivity.
  (* Index 3: 64, Pos 3 (Odd). Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 4: 87 (Odd), Pos 4 (Even). Match. Tail sum = 303 - 87 = 216 *)
  apply soep_match with (s_tail := 216). reflexivity. reflexivity.
  (* Index 5: 75, Pos 5 (Odd). Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 6: 97 (Odd), Pos 6 (Even). Match. Tail sum = 216 - 97 = 119 *)
  apply soep_match with (s_tail := 119). reflexivity. reflexivity.
  (* Index 7: 108, Pos 7 (Odd). Skip. *)
  apply soep_skip. left. reflexivity.
  (* Index 8: 119 (Odd), Pos 8 (Even). Match. Tail sum = 119 - 119 = 0 *)
  apply soep_match with (s_tail := 0). reflexivity. reflexivity.
  (* Index 9: Nil *)
  apply soep_nil.
Qed.