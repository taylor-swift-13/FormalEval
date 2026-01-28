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

Example test_case : problem_121_spec [30; 31; 54; 42; 53; 86; 97; 118; 97] 247.
Proof.
  unfold problem_121_spec.
  (* Index 0: 30. Even index (0), Even value. Skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: 31. Odd index (1). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 54. Even index (2), Even value. Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 42. Odd index (3). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 53. Even index (4), Odd value. Match. *)
           apply soep_match with (s_tail := 194).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 86. Odd index (5). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 97. Even index (6), Odd value. Match. *)
                 apply soep_match with (s_tail := 97).
                 *** reflexivity.
                 *** reflexivity.
                 *** (* Index 7: 118. Odd index (7). Skip. *)
                     apply soep_skip.
                     ---- left. reflexivity.
                     ---- (* Index 8: 97. Even index (8), Odd value. Match. *)
                          apply soep_match with (s_tail := 0).
                          ++++ reflexivity.
                          ++++ reflexivity.
                          ++++ (* Index 9: nil. *)
                               apply soep_nil.
Qed.