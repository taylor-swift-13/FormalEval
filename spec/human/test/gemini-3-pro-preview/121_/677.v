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

Example test_case : problem_121_spec [1; 1; 1; 2; 1; 1; 1; 1; 1; 1] 5.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 1. Position 0 (even), Value 1 (odd). Match. *)
  apply soep_match with (s_tail := 4).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Value 1. Position 1 (odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 1. Position 2 (even), Value 1 (odd). Match. *)
      apply soep_match with (s_tail := 3).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Value 2. Position 3 (odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 1. Position 4 (even), Value 1 (odd). Match. *)
           apply soep_match with (s_tail := 2).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 1. Position 5 (odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 1. Position 6 (even), Value 1 (odd). Match. *)
                 apply soep_match with (s_tail := 1).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 1. Position 7 (odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 1. Position 8 (even), Value 1 (odd). Match. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Value 1. Position 9 (odd). Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Nil. *)
                                  apply soep_nil.
Qed.