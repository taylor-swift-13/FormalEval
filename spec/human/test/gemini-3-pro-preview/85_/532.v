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

Example test_case : problem_85_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 6%Z; 8%Z; 10%Z; 556%Z; 101%Z; 32%Z; 920%Z; 42%Z; 37%Z; 29%Z; 7%Z; 8%Z; 6%Z; 100%Z; 8%Z; 5%Z; 556%Z] 1506%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other; [ left; simpl; reflexivity | ].
  apply seao_other; [ right; simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  apply seao_other; [ right; simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  replace 1506 with (6 + 1500) by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  replace 1500 with (10 + 1490) by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  apply seao_other; [ right; simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  replace 1490 with (920 + 570) by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  apply seao_other; [ right; simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  apply seao_other; [ right; simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  replace 570 with (6 + 564) by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  replace 564 with (8 + 556) by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  apply seao_other; [ left; simpl; reflexivity | ].
  replace 556 with (556 + 0) by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  apply seao_nil.
Qed.