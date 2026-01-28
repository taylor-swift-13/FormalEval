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

Example test_case : problem_121_spec [11; 89; 22; 33; 44; 55; 66; 77; 88; 99] 11.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 11. Pos 0 (even), Val 11 (odd). Match. Need tail sum 0. *)
  apply soep_match with (s_tail := 0).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Value 89. Pos 1 (odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 22. Pos 2 (even), Val 22 (even). Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 33. Pos 3 (odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 44. Pos 4 (even), Val 44 (even). Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: Value 55. Pos 5 (odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 66. Pos 6 (even), Val 66 (even). Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: Value 77. Pos 7 (odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 88. Pos 8 (even), Val 88 (even). Skip. *)
                         apply soep_skip.
                        *** right. reflexivity.
                        *** (* Index 9: Value 99. Pos 9 (odd). Skip. *)
                            apply soep_skip.
                            ---- left. reflexivity.
                            ---- (* Index 10: Nil. *)
                                 apply soep_nil.
Qed.