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

Example test_case : problem_121_spec [31; 75; 10; 53; 87; 97; 118; 75] 118.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Even pos, Odd val. Match. *)
  apply soep_match with (s_tail := 87).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 75. Odd pos. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 10. Even pos, Even val. Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 53. Odd pos. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 87. Even pos, Odd val. Match. *)
           apply soep_match with (s_tail := 0).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 97. Odd pos. Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 118. Even pos, Even val. Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 75. Odd pos. Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Nil. *)
                         apply soep_nil.
Qed.