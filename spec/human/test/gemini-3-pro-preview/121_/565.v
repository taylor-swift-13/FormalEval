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

Example test_case : problem_121_spec [65; 10; 22; 4; 33; 44; 55; 76; 66; 77; 88; 22; 33] 186.
Proof.
  unfold problem_121_spec.
  (* Index 0: 65 (Odd), Pos 0 (Even) -> Match. Remaining sum: 121 *)
  apply soep_match with (s_tail := 121).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 10, Pos 1 (Odd) -> Skip *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 22 (Even), Pos 2 (Even) -> Skip *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 4, Pos 3 (Odd) -> Skip *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 33 (Odd), Pos 4 (Even) -> Match. Remaining sum: 88 *)
           apply soep_match with (s_tail := 88).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 44, Pos 5 (Odd) -> Skip *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 55 (Odd), Pos 6 (Even) -> Match. Remaining sum: 33 *)
                 apply soep_match with (s_tail := 33).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: 76, Pos 7 (Odd) -> Skip *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 66 (Even), Pos 8 (Even) -> Skip *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: 77, Pos 9 (Odd) -> Skip *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 88 (Even), Pos 10 (Even) -> Skip *)
                                  apply soep_skip.
                                  ++++ right. reflexivity.
                                  ++++ (* Index 11: 22, Pos 11 (Odd) -> Skip *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Index 12: 33 (Odd), Pos 12 (Even) -> Match. Remaining sum: 0 *)
                                            apply soep_match with (s_tail := 0).
                                            ----- reflexivity.
                                            ----- reflexivity.
                                            ----- (* Index 13: Nil *)
                                                  apply soep_nil.
Qed.