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

Example test_case : problem_121_spec [31; 120; 42; 53; 75; 86; 97; 76; 75; 75] 278.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Pos 0 (even), Val 31 (odd). Match. *)
  apply soep_match with (s_tail := 247).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 120. Pos 1 (odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 42. Pos 2 (even), Val 42 (even). Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: 53. Pos 3 (odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 75. Pos 4 (even), Val 75 (odd). Match. *)
           apply soep_match with (s_tail := 172).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 86. Pos 5 (odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 97. Pos 6 (even), Val 97 (odd). Match. *)
                 apply soep_match with (s_tail := 75).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: 76. Pos 7 (odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 75. Pos 8 (even), Val 75 (odd). Match. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: 75. Pos 9 (odd). Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- apply soep_nil.
Qed.