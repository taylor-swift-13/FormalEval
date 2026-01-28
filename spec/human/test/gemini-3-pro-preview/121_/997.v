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

Example test_case : problem_121_spec [4; 3; 4; 5; 7; 8; 9] 16.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 4. Position even (0), Value even. Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 3. Position odd (1). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 4. Position even (2), Value even. Apply skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 5. Position odd (3). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 7. Position even (4), Value odd. Apply match. *)
           (* We need 7 + 9 = 16, so s_tail must be 9. *)
           apply soep_match with (s_tail := 9).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 8. Position odd (5). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 9. Position even (6), Value odd. Apply match. *)
                 (* We need 9 + 0 = 9, so s_tail must be 0. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Empty list. Base case. *)
                     apply soep_nil.
Qed.