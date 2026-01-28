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

Example test_case : problem_121_spec [100; 1; 2; 1; 1; 1; 1; 0; 0] 2.
Proof.
  unfold problem_121_spec.
  (* Index 0: 100. Even index, even value. Skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: 1. Odd index. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 2. Even index, even value. Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 1. Odd index. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 1. Even index, odd value. Match. Need remainder 1. *)
           apply soep_match with (s_tail := 1).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 1. Odd index. Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 1. Even index, odd value. Match. Need remainder 0. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: 0. Odd index. Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 0. Even index, even value. Skip. *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: Nil. *)
                             apply soep_nil.
Qed.