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

Example test_case : problem_85_spec [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z; 22%Z; 24%Z; 26%Z; 28%Z; 30%Z; 30%Z] 142%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. reflexivity.
  replace 142%Z with (4 + 138)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 138%Z with (8 + 130)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 130%Z with (12 + 118)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 118%Z with (16 + 102)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 102%Z with (20 + 82)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 82%Z with (24 + 58)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 58%Z with (28 + 30)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 30%Z with (30 + 0)%Z by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_nil.
Qed.