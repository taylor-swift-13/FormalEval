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

Example test_case : problem_121_spec [22; 33; 44; 88; 99; 32] 99.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 22. Position even (0), Value even (22). Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 33. Position odd (1). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 44. Position even (2), Value even (44). Apply skip. *)
      apply soep_skip.
      * right. reflexivity.
      * (* Index 3: Value 88. Position odd (3). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 99. Position even (4), Value odd (99). Apply match. *)
           apply soep_match with (s_tail := 0).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 32. Position odd (5). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Index 6: Empty list. Base case. *)
                 apply soep_nil.
Qed.