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

Example test_case : problem_85_spec [3; 5; 7; 7; 9; 2; 6; 8; 10; 556; 101; 187; 920; 42; 37; 29; 7; 6; 100; 8; 5; 556]%Z 1178%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  replace 1178%Z with (2 + 1176)%Z by reflexivity. apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 1176%Z with (8 + 1168)%Z by reflexivity. apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 1168%Z with (556 + 612)%Z by reflexivity. apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  replace 612%Z with (42 + 570)%Z by reflexivity. apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  replace 570%Z with (6 + 564)%Z by reflexivity. apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 564%Z with (8 + 556)%Z by reflexivity. apply seao_odd_even; try reflexivity.
  apply seao_other. left. reflexivity.
  replace 556%Z with (556 + 0)%Z by reflexivity. apply seao_odd_even; try reflexivity.
  apply seao_nil.
Qed.