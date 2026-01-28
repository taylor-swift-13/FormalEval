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

Example test_case : problem_121_spec [31; 42; 75; 86; 32; 97; 120; 76; 75; 120] 181.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31 is odd, position 0 is even -> Match. Need sum 31 + 150 = 181 *)
  apply soep_match with (s_tail := 150).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Position 1 is odd -> Skip *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 75 is odd, position 2 is even -> Match. Need sum 75 + 75 = 150 *)
      apply soep_match with (s_tail := 75).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Position 3 is odd -> Skip *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 32 is even, position 4 is even -> Skip *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: Position 5 is odd -> Skip *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 120 is even, position 6 is even -> Skip *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: Position 7 is odd -> Skip *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 75 is odd, position 8 is even -> Match. Need sum 75 + 0 = 75 *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Position 9 is odd -> Skip *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Nil -> End *)
                                  apply soep_nil.
Qed.