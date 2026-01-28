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

Example test_case : problem_121_spec [3; 4; 6; 21; 12; 8; 11; 100; 8; 8; 9] 23.
Proof.
  unfold problem_121_spec.
  (* Index 0: 3 (Even pos, Odd val) -> Match. Need sum 20. *)
  apply soep_match with (s_tail := 20).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 4 (Odd pos) -> Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 6 (Even pos, Even val) -> Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 21 (Odd pos) -> Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 12 (Even pos, Even val) -> Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 8 (Odd pos) -> Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 11 (Even pos, Odd val) -> Match. Need sum 9. *)
                 apply soep_match with (s_tail := 9).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: 100 (Odd pos) -> Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 8 (Even pos, Even val) -> Skip. *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: 8 (Odd pos) -> Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 9 (Even pos, Odd val) -> Match. Need sum 0. *)
                                  apply soep_match with (s_tail := 0).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ (* Index 11: Nil *)
                                       apply soep_nil.
Qed.