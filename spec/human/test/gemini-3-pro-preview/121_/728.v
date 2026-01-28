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

Example test_case : problem_121_spec [11; 89; 22; 33; 44; 55; 66; 10; 77; 88; 99; 66] 187.
Proof.
  unfold problem_121_spec.
  (* Index 0: 11 (Odd). Pos 0 (Even). Match. *)
  apply soep_match with (s_tail := 176).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 89. Pos 1 (Odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 22. Pos 2 (Even). Val Even. Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 33. Pos 3 (Odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 44. Pos 4 (Even). Val Even. Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 55. Pos 5 (Odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 66. Pos 6 (Even). Val Even. Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 10. Pos 7 (Odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 77 (Odd). Pos 8 (Even). Match. *)
                         apply soep_match with (s_tail := 99).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: 88. Pos 9 (Odd). Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 99 (Odd). Pos 10 (Even). Match. *)
                                  apply soep_match with (s_tail := 0).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ (* Index 11: 66. Pos 11 (Odd). Skip. *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** apply soep_nil.
Qed.