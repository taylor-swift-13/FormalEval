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

Example test_case : problem_121_spec [31; 42; 3; 64; 87; 75; 86; 97; 108; 119; 31] 152.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Even pos, Odd val. Match. 152 - 31 = 121 *)
  apply soep_match with (s_tail := 121).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 42. Odd pos. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 3. Even pos, Odd val. Match. 121 - 3 = 118 *)
      apply soep_match with (s_tail := 118).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 64. Odd pos. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 87. Even pos, Odd val. Match. 118 - 87 = 31 *)
           apply soep_match with (s_tail := 31).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 75. Odd pos. Skip. *)
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
                             ---- (* Index 10: 31. Even pos, Odd val. Match. 31 - 31 = 0 *)
                                  apply soep_match with (s_tail := 0).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ apply soep_nil.
Qed.