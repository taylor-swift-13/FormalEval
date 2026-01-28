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

Example test_case : problem_121_spec [11; 22; 33; 44; 6; 55; 66; 99; 22; 22; 22; 6] 44.
Proof.
  unfold problem_121_spec.
  (* Index 0: 11 (Even pos, Odd val) -> Match. Tail sum needs to be 33. *)
  apply soep_match with (s_tail := 33); [reflexivity | reflexivity | ].
  (* Index 1: 22 (Odd pos) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 2: 33 (Even pos, Odd val) -> Match. Tail sum needs to be 0. *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity | ].
  (* Index 3: 44 (Odd pos) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 4: 6 (Even pos, Even val) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 5: 55 (Odd pos) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 6: 66 (Even pos, Even val) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 7: 99 (Odd pos) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 8: 22 (Even pos, Even val) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 9: 22 (Odd pos) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* Index 10: 22 (Even pos, Even val) -> Skip. *)
  apply soep_skip; [right; reflexivity | ].
  (* Index 11: 6 (Odd pos) -> Skip. *)
  apply soep_skip; [left; reflexivity | ].
  (* End of list *)
  apply soep_nil.
Qed.