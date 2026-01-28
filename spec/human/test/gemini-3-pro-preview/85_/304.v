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

Example test_case : problem_85_spec [11%Z; 22%Z; 33%Z; 44%Z; 55%Z; 14%Z; 66%Z; 77%Z; 88%Z; 99%Z; 100%Z; 99%Z] 80%Z.
Proof.
  unfold problem_85_spec.
  (* 0: 11 - even index, skip *)
  apply seao_other; [left; simpl; reflexivity |].
  (* 1: 22 - odd index, even value, add 22 *)
  replace 80 with (22 + 58) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity |].
  (* 2: 33 - even index, skip *)
  apply seao_other; [left; simpl; reflexivity |].
  (* 3: 44 - odd index, even value, add 44 *)
  replace 58 with (44 + 14) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity |].
  (* 4: 55 - even index, skip *)
  apply seao_other; [left; simpl; reflexivity |].
  (* 5: 14 - odd index, even value, add 14 *)
  replace 14 with (14 + 0) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity |].
  (* 6: 66 - even index, skip *)
  apply seao_other; [left; simpl; reflexivity |].
  (* 7: 77 - odd index, odd value, skip *)
  apply seao_other; [right; simpl; reflexivity |].
  (* 8: 88 - even index, skip *)
  apply seao_other; [left; simpl; reflexivity |].
  (* 9: 99 - odd index, odd value, skip *)
  apply seao_other; [right; simpl; reflexivity |].
  (* 10: 100 - even index, skip *)
  apply seao_other; [left; simpl; reflexivity |].
  (* 11: 99 - odd index, odd value, skip *)
  apply seao_other; [right; simpl; reflexivity |].
  (* End of list *)
  apply seao_nil.
Qed.