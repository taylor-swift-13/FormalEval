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

Example test_case : problem_121_spec [31; 42; 53; 64; 5; 76; 86; 97; 108; 119; 86] 89.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Even pos, Odd val. Match. *)
  apply soep_match with (s_tail := 58).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 42. Odd pos. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 53. Even pos, Odd val. Match. *)
      apply soep_match with (s_tail := 5).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 64. Odd pos. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 5. Even pos, Odd val. Match. *)
           apply soep_match with (s_tail := 0).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 76. Odd pos. Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 86. Even pos, Even val. Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 97. Odd pos. Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 108. Even pos, Even val. Skip. *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: 119. Odd pos. Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 86. Even pos, Even val. Skip. *)
                                  apply soep_skip.
                                  ++++ right. reflexivity.
                                  ++++ (* End of list *)
                                       apply soep_nil.
Qed.