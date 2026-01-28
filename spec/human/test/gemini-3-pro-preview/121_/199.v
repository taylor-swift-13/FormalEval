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

Example test_case : problem_121_spec [1; 1; 1; 2; 1; 1; 1; 1; 97; 1; 1; 1] 102.
Proof.
  unfold problem_121_spec.
  (* Idx 0: 1, Even pos, Odd val -> Match. 102 - 1 = 101 *)
  apply soep_match with (s_tail := 101).
  - reflexivity.
  - reflexivity.
  - (* Idx 1: 1, Odd pos -> Skip *)
    apply soep_skip.
    + left. reflexivity.
    + (* Idx 2: 1, Even pos, Odd val -> Match. 101 - 1 = 100 *)
      apply soep_match with (s_tail := 100).
      * reflexivity.
      * reflexivity.
      * (* Idx 3: 2, Odd pos -> Skip *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Idx 4: 1, Even pos, Odd val -> Match. 100 - 1 = 99 *)
           apply soep_match with (s_tail := 99).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Idx 5: 1, Odd pos -> Skip *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Idx 6: 1, Even pos, Odd val -> Match. 99 - 1 = 98 *)
                 apply soep_match with (s_tail := 98).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Idx 7: 1, Odd pos -> Skip *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Idx 8: 97, Even pos, Odd val -> Match. 98 - 97 = 1 *)
                         apply soep_match with (s_tail := 1).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Idx 9: 1, Odd pos -> Skip *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Idx 10: 1, Even pos, Odd val -> Match. 1 - 1 = 0 *)
                                  apply soep_match with (s_tail := 0).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ (* Idx 11: 1, Odd pos -> Skip *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Idx 12: Nil -> Base *)
                                            apply soep_nil.
Qed.