Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_even_at_odd_indices_rel : list Z -> nat -> Z -> Prop :=
| seao_nil : forall i, sum_even_at_odd_indices_rel nil i 0%Z
| seao_odd_even : forall h t i s_tail, Nat.odd i = true -> Z.even h = true ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i (h + s_tail)
| seao_other : forall h t i s_tail, (Nat.odd i = false \/ Z.even h = false) ->
    sum_even_at_odd_indices_rel t (S i) s_tail ->
    sum_even_at_odd_indices_rel (h :: t) i s_tail.

Definition problem_85_pre (lst : list Z) : Prop := lst <> []%list.

Definition problem_85_spec (lst : list Z) (output : Z) : Prop :=
  sum_even_at_odd_indices_rel lst 0%nat output.

Example test_case : problem_85_spec [1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 8%Z; 11%Z; 13%Z; 4%Z; 4%Z; 6%Z; 8%Z; 9%Z; 12%Z; 14%Z; 11%Z] 32%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 1: 3. Odd, but not even. *)
  apply seao_other; [right; reflexivity | ].
  (* Index 2: 5. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 3: 7. Odd, but not even. *)
  apply seao_other; [right; reflexivity | ].
  (* Index 4: 9. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 5: 8. Odd and even. Accumulate 8. Remaining sum 24. *)
  replace 32%Z with (8 + 24)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 11. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 7: 13. Odd, but not even. *)
  apply seao_other; [right; reflexivity | ].
  (* Index 8: 4. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 9: 4. Odd and even. Accumulate 4. Remaining sum 20. *)
  replace 24%Z with (4 + 20)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 10: 6. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 11: 8. Odd and even. Accumulate 8. Remaining sum 12. *)
  replace 20%Z with (8 + 12)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 12: 9. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 13: 12. Odd and even. Accumulate 12. Remaining sum 0. *)
  replace 12%Z with (12 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 14: 14. Not odd. *)
  apply seao_other; [left; reflexivity | ].
  (* Index 15: 11. Odd, but not even. *)
  apply seao_other; [right; reflexivity | ].
  (* End of list *)
  apply seao_nil.
Qed.