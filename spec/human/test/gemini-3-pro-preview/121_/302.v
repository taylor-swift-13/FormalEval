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

Example test_case : problem_121_spec [86; 2; 21; 4; 4; 6; 7; 8; 9; 10; 7] 44.
Proof.
  unfold problem_121_spec.
  (* Index 0: 86. Even pos, Even val -> Skip (right) *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: 2. Odd pos -> Skip (left) *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 21. Even pos, Odd val -> Match. Tail sum = 44 - 21 = 23 *)
      apply soep_match with (s_tail := 23).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 4. Odd pos -> Skip (left) *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 4. Even pos, Even val -> Skip (right) *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 6. Odd pos -> Skip (left) *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 7. Even pos, Odd val -> Match. Tail sum = 23 - 7 = 16 *)
                 apply soep_match with (s_tail := 16).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: 8. Odd pos -> Skip (left) *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 9. Even pos, Odd val -> Match. Tail sum = 16 - 9 = 7 *)
                         apply soep_match with (s_tail := 7).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: 10. Odd pos -> Skip (left) *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 7. Even pos, Odd val -> Match. Tail sum = 7 - 7 = 0 *)
                                  apply soep_match with (s_tail := 0).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ (* Index 11: Nil *)
                                       apply soep_nil.
Qed.