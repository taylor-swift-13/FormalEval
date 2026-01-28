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

Example test_case : problem_121_spec [4; 2; 4; 4; 6; 9; 12; 8; 11; 12; 10; 8] 11.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 4 (Even), Position 0 (Even) -> Skip *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 2, Position 1 (Odd) -> Skip *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 4 (Even), Position 2 (Even) -> Skip *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 4, Position 3 (Odd) -> Skip *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 6 (Even), Position 4 (Even) -> Skip *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: Value 9, Position 5 (Odd) -> Skip *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 12 (Even), Position 6 (Even) -> Skip *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: Value 8, Position 7 (Odd) -> Skip *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 11 (Odd), Position 8 (Even) -> Match *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Value 12, Position 9 (Odd) -> Skip *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Value 10 (Even), Position 10 (Even) -> Skip *)
                                  apply soep_skip.
                                  ++++ right. reflexivity.
                                  ++++ (* Index 11: Value 8, Position 11 (Odd) -> Skip *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* End of list *)
                                            apply soep_nil.
Qed.