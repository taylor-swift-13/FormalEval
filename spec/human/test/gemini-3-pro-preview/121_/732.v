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

Example test_case : problem_121_spec [2; 3; 4; 5; 6; 9; 8; 11; 10; 8] 0.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 2. Position is even, Value is even. Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 3. Position is odd. Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 4. Position is even, Value is even. Apply skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 5. Position is odd. Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 6. Position is even, Value is even. Apply skip. *)
           apply soep_skip.
           ++ right. reflexivity.
           ++ (* Index 5: Value 9. Position is odd. Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Value 8. Position is even, Value is even. Apply skip. *)
                 apply soep_skip.
                 --- right. reflexivity.
                 --- (* Index 7: Value 11. Position is odd. Apply skip. *)
                     apply soep_skip.
                     +++ left. reflexivity.
                     +++ (* Index 8: Value 10. Position is even, Value is even. Apply skip. *)
                         apply soep_skip.
                         *** right. reflexivity.
                         *** (* Index 9: Value 8. Position is odd. Apply skip. *)
                             apply soep_skip.
                             ---- left. reflexivity.
                             ---- (* Base case *)
                                  apply soep_nil.
Qed.