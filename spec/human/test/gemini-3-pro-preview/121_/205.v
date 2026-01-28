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

Example test_case : problem_121_spec [1; 1; 1; 2; 1; 1; 1; 1; 1; 97; 1; 1; 1] 7.
Proof.
  unfold problem_121_spec.
  (* Index 0: Val 1. Even pos (0), Odd val. Match. *)
  apply soep_match with (s_tail := 6).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Val 1. Odd pos (1). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Val 1. Even pos (2), Odd val. Match. *)
      apply soep_match with (s_tail := 5).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Val 2. Odd pos (3). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Val 1. Even pos (4), Odd val. Match. *)
           apply soep_match with (s_tail := 4).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Val 1. Odd pos (5). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Val 1. Even pos (6), Odd val. Match. *)
                 apply soep_match with (s_tail := 3).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Val 1. Odd pos (7). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Val 1. Even pos (8), Odd val. Match. *)
                         apply soep_match with (s_tail := 2).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Val 97. Odd pos (9). Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Val 1. Even pos (10), Odd val. Match. *)
                                  apply soep_match with (s_tail := 1).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ (* Index 11: Val 1. Odd pos (11). Skip. *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Index 12: Val 1. Even pos (12), Odd val. Match. *)
                                            apply soep_match with (s_tail := 0).
                                            ----- reflexivity.
                                            ----- reflexivity.
                                            ----- (* Index 13: Nil. *)
                                                  apply soep_nil.
Qed.