Require Import Coq.Arith.Arith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.

Inductive sum_odd_in_even_pos_rel : list nat -> nat -> nat -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel nil i 0
| soep_match : forall h t i s_tail, Nat.even i = true -> Nat.even h = false ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Nat.even i = false \/ Nat.even h = true) ->
    sum_odd_in_even_pos_rel t (S i) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

Example test_case : sum_odd_in_even_pos_rel [5; 8; 7; 1] 0 12.
Proof.
  apply soep_match.
  - compute. reflexivity.
  - compute. reflexivity.
  - apply soep_skip.
    + left. compute. reflexivity.
    + apply soep_match.
      * compute. reflexivity.
      * compute. reflexivity.
      * apply soep_skip.
        { left. compute. reflexivity. }
        { apply soep_nil. }
Qed.