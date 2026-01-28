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

Example test_case : problem_85_spec [11%Z; 22%Z; 33%Z; 12%Z; 44%Z; 54%Z; 14%Z; 66%Z; 77%Z; 88%Z; 2%Z; 99%Z; 44%Z; 99%Z] 242%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. reflexivity.
  replace 242%Z with (22 + 220)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 220%Z with (12 + 208)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 208%Z with (54 + 154)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 154%Z with (66 + 88)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 88%Z with (88 + 0)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_nil.
Qed.