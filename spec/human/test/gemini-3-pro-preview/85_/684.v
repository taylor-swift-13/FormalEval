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

Example test_case : problem_85_spec [2%Z; 4%Z; 6%Z; 17%Z; 10%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z; 17%Z; 24%Z; 13%Z; 28%Z; 30%Z; 6%Z; 4%Z; 2%Z; 4%Z] 120%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. reflexivity.
  replace 120 with (4 + 116) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  replace 116 with (8 + 108) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 108 with (12 + 96) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 96 with (16 + 80) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 80 with (20 + 60) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 60 with (24 + 36) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 36 with (28 + 8) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 8 with (6 + 2) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 2 with (2 + 0) by reflexivity.
  apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_nil.
Qed.