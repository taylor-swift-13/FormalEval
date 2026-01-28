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

Example test_case : problem_121_spec [1; 1; 44; 1; 44; 1; 1; 1; 1; 1; 97; 1; 1; 1] 101.
Proof.
  unfold problem_121_spec.
  (* Index 0: 1. Even pos, Odd val. Match. Remainder 100. *)
  apply soep_match with (s_tail := 100).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 1. Odd pos. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 44. Even pos, Even val. Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 1. Odd pos. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 44. Even pos, Even val. Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 1. Odd pos. Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 1. Even pos, Odd val. Match. Remainder 99. *)
                 apply soep_match with (s_tail := 99).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: 1. Odd pos. Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 1. Even pos, Odd val. Match. Remainder 98. *)
                         apply soep_match with (s_tail := 98).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: 1. Odd pos. Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 97. Even pos, Odd val. Match. Remainder 1. *)
                                  apply soep_match with (s_tail := 1).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ (* Index 11: 1. Odd pos. Skip. *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Index 12: 1. Even pos, Odd val. Match. Remainder 0. *)
                                            apply soep_match with (s_tail := 0).
                                            ----- reflexivity.
                                            ----- reflexivity.
                                            ----- (* Index 13: 1. Odd pos. Skip. *)
                                                  apply soep_skip.
                                                  +++++ left. reflexivity.
                                                  +++++ apply soep_nil.
Qed.