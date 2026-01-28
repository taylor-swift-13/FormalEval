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

Example test_case : problem_121_spec [2; 2; 1; 1; 1; 5; 5; 98; 2] 7.
Proof.
  unfold problem_121_spec.
  (* Index 0: Val 2. Pos Even (0), Val Even. Skip (right). *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Val 2. Pos Odd (1). Skip (left). *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Val 1. Pos Even (2), Val Odd. Match. Need 1 + 6 = 7. *)
      apply soep_match with (s_tail := 6).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Val 1. Pos Odd (3). Skip (left). *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Val 1. Pos Even (4), Val Odd. Match. Need 1 + 5 = 6. *)
           apply soep_match with (s_tail := 5).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Val 5. Pos Odd (5). Skip (left). *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Val 5. Pos Even (6), Val Odd. Match. Need 5 + 0 = 5. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Val 98. Pos Odd (7). Skip (left). *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Val 2. Pos Even (8), Val Even. Skip (right). *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: Nil. *)
                             apply soep_nil.
Qed.