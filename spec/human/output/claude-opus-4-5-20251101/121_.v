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

Example test_problem_121 : problem_121_spec [5; 8; 7; 1] 12.
Proof.
  unfold problem_121_spec.
  (* 12 = 5 + 7 = 5 + (7 + 0) *)
  (* Position 0: 5 is odd, position is even -> add 5, need to show 12 = 5 + 7 *)
  replace 12 with (5 + 7) by reflexivity.
  apply soep_match.
  - reflexivity.
  - reflexivity.
  - (* Position 1: 8 is even, position is odd -> skip *)
    apply soep_skip.
    + right. reflexivity.
    + (* Position 2: 7 is odd, position is even -> add 7 *)
      replace 7 with (7 + 0) by reflexivity.
      apply soep_match.
      * reflexivity.
      * reflexivity.
      * (* Position 3: 1 is odd, position is odd -> skip *)
        apply soep_skip.
        -- left. reflexivity.
        -- apply soep_nil.
Qed.