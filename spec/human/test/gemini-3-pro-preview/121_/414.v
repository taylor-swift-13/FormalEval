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

Example test_case : problem_121_spec [9; 65; 22; 33; 44; 66; 77; 88] 86.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 9 (Odd), Pos 0 (Even). Match. Tail sum needs to be 77. *)
  apply soep_match with (s_tail := 77).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Value 65, Pos 1 (Odd). Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 22 (Even), Pos 2 (Even). Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 33, Pos 3 (Odd). Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 44 (Even), Pos 4 (Even). Skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: Value 66, Pos 5 (Odd). Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 77 (Odd), Pos 6 (Even). Match. Tail sum 0. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 88, Pos 7 (Odd). Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Nil. *)
                         apply soep_nil.
Qed.