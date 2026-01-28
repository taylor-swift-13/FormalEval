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

Example test_case : problem_121_spec [31; 120; 42; 55; 53; 75; 86; 97; 52; 119; 75; 75] 159.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Pos 0 (even), Val 31 (odd). Match. Remainder: 159 - 31 = 128 *)
  apply soep_match with (s_tail := 128).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 120. Pos 1 (odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 42. Pos 2 (even), Val 42 (even). Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 55. Pos 3 (odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 53. Pos 4 (even), Val 53 (odd). Match. Remainder: 128 - 53 = 75 *)
           apply soep_match with (s_tail := 75).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 75. Pos 5 (odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 86. Pos 6 (even), Val 86 (even). Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 97. Pos 7 (odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 52. Pos 8 (even), Val 52 (even). Skip. *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: 119. Pos 9 (odd). Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 75. Pos 10 (even), Val 75 (odd). Match. Remainder: 75 - 75 = 0 *)
                                  apply soep_match with (s_tail := 0).
                                  ++++ reflexivity.
                                  ++++ reflexivity.
                                  ++++ (* Index 11: 75. Pos 11 (odd). Skip. *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Index 12: Nil. *)
                                            apply soep_nil.
Qed.