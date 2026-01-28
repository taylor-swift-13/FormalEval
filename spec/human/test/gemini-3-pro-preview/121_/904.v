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

Example test_case : problem_121_spec [31; 42; 53; 75; 86; 97; 52; 119; 75; 75; 75] 234.
Proof.
  unfold problem_121_spec.
  (* Index 0: 31 (Odd), Pos 0 (Even). Match. Sum += 31. Rem: 203 *)
  apply soep_match with (s_tail := 203).
  - reflexivity.
  - reflexivity.
  - (* Index 1: 42, Pos 1 (Odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: 53 (Odd), Pos 2 (Even). Match. Sum += 53. Rem: 150 *)
      apply soep_match with (s_tail := 150).
      * reflexivity.
      * reflexivity.
      * (* Index 3: 75, Pos 3 (Odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: 86 (Even), Pos 4 (Even). Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: 97, Pos 5 (Odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: 52 (Even), Pos 6 (Even). Skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: 119, Pos 7 (Odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: 75 (Odd), Pos 8 (Even). Match. Sum += 75. Rem: 75 *)
                         apply soep_match with (s_tail := 75).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: 75, Pos 9 (Odd). Skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: 75 (Odd), Pos 10 (Even). Match. Sum += 75. Rem: 0 *)
                                  apply soep_match with (s_tail := 0).
                                  **** reflexivity.
                                  **** reflexivity.
                                  **** (* Index 11: Nil. *)
                                       apply soep_nil.
Qed.