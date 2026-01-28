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

Example test_case : problem_121_spec [65; 11; 22; 33; 44; 55; 66; 77; 88; 77; 99] 164.
Proof.
  unfold problem_121_spec.
  (* Index 0: 65. Even pos, Odd val -> Match. s_tail = 164 - 65 = 99 *)
  apply soep_match with (s_tail := 99).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 11. Odd pos -> Skip *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 22. Even pos, Even val -> Skip *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 33. Odd pos -> Skip *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 44. Even pos, Even val -> Skip *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 55. Odd pos -> Skip *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 66. Even pos, Even val -> Skip *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 77. Odd pos -> Skip *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 88. Even pos, Even val -> Skip *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: 77. Odd pos -> Skip *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 99. Even pos, Odd val -> Match. s_tail = 0 *)
                                  apply soep_match with (s_tail := 0).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ apply soep_nil.
Qed.