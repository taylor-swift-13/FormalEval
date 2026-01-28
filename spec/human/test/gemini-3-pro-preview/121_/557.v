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

Example test_case : problem_121_spec [3; 3; 9; 4; 4; 6; 7; 9; 12; 8; 11; 10; 10; 10; 8; 10; 12; 8] 30.
Proof.
  unfold problem_121_spec.
  (* Index 0: 3 (even index, odd value) -> Match. Remaining sum 27. *)
  apply soep_match with (s_tail := 27); [reflexivity | reflexivity | ].
  (* Index 1: 3 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 2: 9 (even index, odd value) -> Match. Remaining sum 18. *)
  apply soep_match with (s_tail := 18); [reflexivity | reflexivity | ].
  (* Index 3: 4 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 4: 4 (even index, even value) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 5: 6 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 6: 7 (even index, odd value) -> Match. Remaining sum 11. *)
  apply soep_match with (s_tail := 11); [reflexivity | reflexivity | ].
  (* Index 7: 9 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 8: 12 (even index, even value) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 9: 8 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 10: 11 (even index, odd value) -> Match. Remaining sum 0. *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity | ].
  (* Index 11: 10 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 12: 10 (even index, even value) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 13: 10 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 14: 8 (even index, even value) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 15: 10 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 16: 12 (even index, even value) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 17: 8 (odd index) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* End of list *)
  apply soep_nil.
Qed.