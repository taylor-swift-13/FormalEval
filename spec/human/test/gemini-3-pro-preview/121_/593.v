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

Example test_case : problem_121_spec [0; 74; 53; 2; 3; 5; 6; 8; 9; 10] 65.
Proof.
  unfold problem_121_spec.
  (* Index 0: 0. Even index, Even value -> Skip *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: 74. Odd index -> Skip *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 53. Even index, Odd value -> Match. Need 53 + 12 = 65 *)
      apply soep_match with (s_tail := 12).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 2. Odd index -> Skip *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 3. Even index, Odd value -> Match. Need 3 + 9 = 12 *)
           apply soep_match with (s_tail := 9).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 5. Odd index -> Skip *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 6. Even index, Even value -> Skip *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 8. Odd index -> Skip *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 9. Even index, Odd value -> Match. Need 9 + 0 = 9 *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: 10. Odd index -> Skip *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Nil *)
                                  apply soep_nil.
Qed.