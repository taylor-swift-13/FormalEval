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

Example test_case : problem_121_spec [31; 42; 53; 86; 97; 87; 118; 42] 181.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31. Pos 0 (even), Val 31 (odd). Match. Rem: 150 *)
  apply soep_match with (s_tail := 150).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 42. Pos 1 (odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 53. Pos 2 (even), Val 53 (odd). Match. Rem: 97 *)
      apply soep_match with (s_tail := 97).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 86. Pos 3 (odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 97. Pos 4 (even), Val 97 (odd). Match. Rem: 0 *)
           apply soep_match with (s_tail := 0).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: 87. Pos 5 (odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 118. Pos 6 (even), Val 118 (even). Skip. *)
                 apply soep_skip.
                 *** right. reflexivity.
                 *** (* Index 7: 42. Pos 7 (odd). Skip. *)
                     apply soep_skip.
                     ---- left. reflexivity.
                     ---- apply soep_nil.
Qed.