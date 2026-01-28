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

Example test_case : problem_121_spec [3; 3; 5; 6; 6; 44; 8; 8; 5] 13.
Proof.
  unfold problem_121_spec.
  (* Index 0: 3. Even pos (0), Odd val (3). Match. Need 10. *)
  apply soep_match with (s_tail := 10).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 3. Odd pos (1). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 5. Even pos (2), Odd val (5). Match. Need 5. *)
      apply soep_match with (s_tail := 5).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 6. Odd pos (3). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 6. Even pos (4), Even val (6). Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 44. Odd pos (5). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 8. Even pos (6), Even val (8). Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 8. Odd pos (7). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 5. Even pos (8), Odd val (5). Match. Need 0. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Nil. *)
                             apply soep_nil.
Qed.