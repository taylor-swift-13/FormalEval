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

Example test_case : problem_85_spec [1%Z; 3%Z; 5%Z; 7%Z; 9%Z; 11%Z; 13%Z; 2%Z; 4%Z; 6%Z; 8%Z; 8%Z; 10%Z; 12%Z; 14%Z; 8%Z] 36%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 1: 3. Odd index, odd value. *)
  apply seao_other. right; simpl; reflexivity.
  (* Index 2: 5. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 3: 7. Odd index, odd value. *)
  apply seao_other. right; simpl; reflexivity.
  (* Index 4: 9. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 5: 11. Odd index, odd value. *)
  apply seao_other. right; simpl; reflexivity.
  (* Index 6: 13. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 7: 2. Odd index, even value. Sum 36 = 2 + 34. *)
  replace 36 with (2 + 34) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 8: 4. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 9: 6. Odd index, even value. Sum 34 = 6 + 28. *)
  replace 34 with (6 + 28) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 10: 8. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 11: 8. Odd index, even value. Sum 28 = 8 + 20. *)
  replace 28 with (8 + 20) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 12: 10. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 13: 12. Odd index, even value. Sum 20 = 12 + 8. *)
  replace 20 with (12 + 8) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 14: 14. Not odd index. *)
  apply seao_other. left; simpl; reflexivity.
  (* Index 15: 8. Odd index, even value. Sum 8 = 8 + 0. *)
  replace 8 with (8 + 0) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 16: nil. *)
  apply seao_nil.
Qed.