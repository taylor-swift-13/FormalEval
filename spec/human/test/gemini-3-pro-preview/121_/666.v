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

Example test_case : problem_121_spec [31; 42; 42; 53; 75; 86; 97; 120; 75] 278.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 31. Pos 0 is even, Val 31 is odd. Match. *)
  (* Need 31 + 247 = 278 *)
  apply soep_match with (s_tail := 247).
  - reflexivity.
  - reflexivity.
  - (* Index 1: Value 42. Pos 1 is odd. Skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 42. Pos 2 is even, Val 42 is even. Skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 53. Pos 3 is odd. Skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 75. Pos 4 is even, Val 75 is odd. Match. *)
           (* Need 75 + 172 = 247 *)
           apply soep_match with (s_tail := 172).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 86. Pos 5 is odd. Skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 97. Pos 6 is even, Val 97 is odd. Match. *)
                 (* Need 97 + 75 = 172 *)
                 apply soep_match with (s_tail := 75).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 120. Pos 7 is odd. Skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 75. Pos 8 is even, Val 75 is odd. Match. *)
                         (* Need 75 + 0 = 75 *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Nil *)
                             apply soep_nil.
Qed.