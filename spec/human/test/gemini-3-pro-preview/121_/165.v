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

Example test_case : problem_121_spec [2; 11; 3; 4; 5; 88; 6; 9; 8; 55; 11; 10; 8; 8] 19.
Proof.
  unfold problem_121_spec.
  (* Index 0: 2 (even index, even value) -> skip *)
  apply soep_skip; [ right; reflexivity | ].
  (* Index 1: 11 (odd index) -> skip *)
  apply soep_skip; [ left; reflexivity | ].
  (* Index 2: 3 (even index, odd value) -> match, need sum 16 *)
  apply soep_match with (s_tail := 16); [ reflexivity | reflexivity | ].
  (* Index 3: 4 (odd index) -> skip *)
  apply soep_skip; [ left; reflexivity | ].
  (* Index 4: 5 (even index, odd value) -> match, need sum 11 *)
  apply soep_match with (s_tail := 11); [ reflexivity | reflexivity | ].
  (* Index 5: 88 (odd index) -> skip *)
  apply soep_skip; [ left; reflexivity | ].
  (* Index 6: 6 (even index, even value) -> skip *)
  apply soep_skip; [ right; reflexivity | ].
  (* Index 7: 9 (odd index) -> skip *)
  apply soep_skip; [ left; reflexivity | ].
  (* Index 8: 8 (even index, even value) -> skip *)
  apply soep_skip; [ right; reflexivity | ].
  (* Index 9: 55 (odd index) -> skip *)
  apply soep_skip; [ left; reflexivity | ].
  (* Index 10: 11 (even index, odd value) -> match, need sum 0 *)
  apply soep_match with (s_tail := 0); [ reflexivity | reflexivity | ].
  (* Index 11: 10 (odd index) -> skip *)
  apply soep_skip; [ left; reflexivity | ].
  (* Index 12: 8 (even index, even value) -> skip *)
  apply soep_skip; [ right; reflexivity | ].
  (* Index 13: 8 (odd index) -> skip *)
  apply soep_skip; [ left; reflexivity | ].
  (* Index 14: nil *)
  apply soep_nil.
Qed.