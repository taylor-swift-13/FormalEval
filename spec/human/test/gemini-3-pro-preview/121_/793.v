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

Example test_case : problem_121_spec [0; 1; 2; 3; 10; 4; 5; 7; 8; 1; 2; 2] 5.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 0. Position even (0), Value even (0). Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 1. Position odd (1). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 2. Position even (2), Value even (2). Apply skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 3. Position odd (3). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 10. Position even (4), Value even (10). Apply skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: Value 4. Position odd (5). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 5. Position even (6), Value odd (5). Apply match. *)
                 (* We need 5 + 0 = 5, so s_tail must be 0. *)
                 apply soep_match with (s_tail := 0).
                 --- reflexivity.
                 --- reflexivity.
                 --- (* Index 7: Value 7. Position odd (7). Apply skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 8. Position even (8), Value even (8). Apply skip. *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: Value 1. Position odd (9). Apply skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Index 10: Value 2. Position even (10), Value even (2). Apply skip. *)
                                  apply soep_skip.
                                  ++++ right. reflexivity.
                                  ++++ (* Index 11: Value 2. Position odd (11). Apply skip. *)
                                       apply soep_skip.
                                       **** left. reflexivity.
                                       **** (* Index 12: Empty list. Base case. *)
                                            apply soep_nil.
Qed.