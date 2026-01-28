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

Example test_case : problem_121_spec [2; 3; 5; 6; 9; 8; 11; 10] 25.
Proof.
  unfold problem_121_spec.
  (* Index 0: Val 2 (Even), Pos 0 (Even). Skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Val 3, Pos 1 (Odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Val 5 (Odd), Pos 2 (Even). Match. *)
      apply soep_match with (s_tail := 20).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Val 6, Pos 3 (Odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Val 9 (Odd), Pos 4 (Even). Match. *)
           apply soep_match with (s_tail := 11).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Val 8, Pos 5 (Odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Val 11 (Odd), Pos 6 (Even). Match. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Val 10, Pos 7 (Odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* End of list *)
                         apply soep_nil.
Qed.