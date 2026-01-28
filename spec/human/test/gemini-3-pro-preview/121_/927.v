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

Example test_case : problem_121_spec [1; 1; 1; 120; 119; 119; 1; 1; 119; 1] 241.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 1. Even pos, Odd val. Match. Need 1 + 240 = 241. *)
  apply soep_match with (s_tail := 240).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Value 1. Odd pos. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 1. Even pos, Odd val. Match. Need 1 + 239 = 240. *)
      apply soep_match with (s_tail := 239).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Value 120. Odd pos. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 119. Even pos, Odd val. Match. Need 119 + 120 = 239. *)
           apply soep_match with (s_tail := 120).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 119. Odd pos. Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 1. Even pos, Odd val. Match. Need 1 + 119 = 120. *)
                 apply soep_match with (s_tail := 119).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 1. Odd pos. Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 119. Even pos, Odd val. Match. Need 119 + 0 = 119. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Value 1. Odd pos. Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Nil. *)
                                  apply soep_nil.
Qed.