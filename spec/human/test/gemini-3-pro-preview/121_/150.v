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

Definition problem_121_pre (l : list nat) : Prop := l <> [].

Definition problem_121_spec (l : list nat) (output : nat) : Prop :=
  sum_odd_in_even_pos_rel l 0%nat output.

Example test_case : problem_121_spec [11; 22; 33; 44; 65; 55; 66; 88; 99; 22] 208.
Proof.
  unfold problem_121_spec.
  (* Index 0: 11. Even pos, Odd val. Match. 11 + 197 = 208 *)
  apply soep_match with (s_tail := 197); [reflexivity | reflexivity |].
  (* Index 1: 22. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 2: 33. Even pos, Odd val. Match. 33 + 164 = 197 *)
  apply soep_match with (s_tail := 164); [reflexivity | reflexivity |].
  (* Index 3: 44. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 4: 65. Even pos, Odd val. Match. 65 + 99 = 164 *)
  apply soep_match with (s_tail := 99); [reflexivity | reflexivity |].
  (* Index 5: 55. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 6: 66. Even pos, Even val. Skip. *)
  apply soep_skip; [right; reflexivity |].
  (* Index 7: 88. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Index 8: 99. Even pos, Odd val. Match. 99 + 0 = 99 *)
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity |].
  (* Index 9: 22. Odd pos. Skip. *)
  apply soep_skip; [left; reflexivity |].
  (* Nil *)
  apply soep_nil.
Qed.