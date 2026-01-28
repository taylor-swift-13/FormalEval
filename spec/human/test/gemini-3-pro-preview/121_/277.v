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

Example test_case : problem_121_spec [11; 22; 33; 44; 65; 55; 66; 88; 99; 0; 22; 33; 88] 208.
Proof.
  unfold problem_121_spec.
  (* Index 0: 11. Even pos, Odd val. Match. Need 208 - 11 = 197. *)
  apply soep_match with (s_tail := 197).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 22. Odd pos. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 33. Even pos, Odd val. Match. Need 197 - 33 = 164. *)
      apply soep_match with (s_tail := 164).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 44. Odd pos. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 65. Even pos, Odd val. Match. Need 164 - 65 = 99. *)
           apply soep_match with (s_tail := 99).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 55. Odd pos. Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 66. Even pos, Even val. Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 88. Odd pos. Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 99. Even pos, Odd val. Match. Need 99 - 99 = 0. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: 0. Odd pos. Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 22. Even pos, Even val. Skip. *)
                                  apply soep_skip.
                                  ++++ right. reflexivity.
                                  ++++ (* Index 11: 33. Odd pos. Skip. *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Index 12: 88. Even pos, Even val. Skip. *)
                                            apply soep_skip.
                                            ----- right. reflexivity.
                                            ----- (* Index 13: Nil. *)
                                                  apply soep_nil.
Qed.