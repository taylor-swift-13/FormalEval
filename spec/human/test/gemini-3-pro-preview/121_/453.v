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

Example test_case : problem_121_spec [99; 4; 1; 4; 1; 4; 1; 4] 102.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 99. Position even (0), Value odd. Match. *)
  apply soep_match with (s_tail := 3).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Value 4. Position odd (1). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 1. Position even (2), Value odd. Match. *)
      apply soep_match with (s_tail := 2).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Value 4. Position odd (3). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 1. Position even (4), Value odd. Match. *)
           apply soep_match with (s_tail := 1).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 4. Position odd (5). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 1. Position even (6), Value odd. Match. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 4. Position odd (7). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Nil. *)
                         apply soep_nil.
Qed.