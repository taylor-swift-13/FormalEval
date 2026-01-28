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

Example test_case : problem_121_spec [0; 2; 3; 4; 5; 6; 7; 8; 77; 10] 92.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 0. Position 0 (even), Value 0 (even). Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 2. Position 1 (odd). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 3. Position 2 (even), Value 3 (odd). Apply match. *)
      (* We need 3 + 89 = 92. *)
      apply soep_match with (s_tail := 89).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Value 4. Position 3 (odd). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 5. Position 4 (even), Value 5 (odd). Apply match. *)
           (* We need 5 + 84 = 89. *)
           apply soep_match with (s_tail := 84).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 6. Position 5 (odd). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 7. Position 6 (even), Value 7 (odd). Apply match. *)
                 (* We need 7 + 77 = 84. *)
                 apply soep_match with (s_tail := 77).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 8. Position 7 (odd). Apply skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 77. Position 8 (even), Value 77 (odd). Apply match. *)
                         (* We need 77 + 0 = 77. *)
                         apply soep_match with (s_tail := 0).
                         *** reflexivity.
                         *** reflexivity.
                         *** (* Index 9: Value 10. Position 9 (odd). Apply skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* End of list *)
                                  apply soep_nil.
Qed.