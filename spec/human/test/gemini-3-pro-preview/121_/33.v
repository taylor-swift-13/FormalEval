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

Example test_case : problem_121_spec [0; 1; 3; 5; 7; 5] 10.
Proof.
  unfold problem_121_spec.
  (* Index 0: Value 0. Even index (0), Value is even (0). Apply skip. *)
  apply soep_skip.
  - right. reflexivity.
  - (* Index 1: Value 1. Odd index (1). Apply skip. *)
    apply soep_skip.
    + left. reflexivity.
    + (* Index 2: Value 3. Even index (2), Value is odd (3). Apply match. *)
      (* We need 3 + 7 = 10, so s_tail must be 7. *)
      apply soep_match with (s_tail := 7).
      * reflexivity.
      * reflexivity.
      * (* Index 3: Value 5. Odd index (3). Apply skip. *)
        apply soep_skip.
        -- left. reflexivity.
        -- (* Index 4: Value 7. Even index (4), Value is odd (7). Apply match. *)
           (* We need 7 + 0 = 7, so s_tail must be 0. *)
           apply soep_match with (s_tail := 0).
           ++ reflexivity.
           ++ reflexivity.
           ++ (* Index 5: Value 5. Odd index (5). Apply skip. *)
              apply soep_skip.
              ** left. reflexivity.
              ** (* Empty list. Base case. *)
                 apply soep_nil.
Qed.