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

Example test_case : problem_121_spec [65; 22; 44; 55; 66; 77] 65.
Proof.
  unfold problem_121_spec.
  (* Index 0: 65. Even pos (0), Odd val (65). Match. Sum = 65 + tail_sum. *)
  apply soep_match with (s_tail := 0).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 22. Odd pos (1). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 44. Even pos (2), Even val (44). Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 55. Odd pos (3). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 66. Even pos (4), Even val (66). Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 77. Odd pos (5). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: []. Base case. *)
                 apply soep_nil.
Qed.