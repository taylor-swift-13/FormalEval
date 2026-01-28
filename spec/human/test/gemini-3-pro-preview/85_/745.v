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

Example test_case : problem_85_spec [2%Z; 4%Z; 8%Z; 10%Z; 12%Z; 16%Z; 14%Z; 18%Z; 20%Z; 22%Z; 24%Z; 26%Z; 28%Z; 30%Z; 30%Z; 16%Z; 22%Z] 142%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left; reflexivity.
  replace 142 with (4 + 138) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 138 with (10 + 128) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 128 with (16 + 112) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 112 with (18 + 94) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 94 with (22 + 72) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 72 with (26 + 46) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 46 with (30 + 16) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 16 with (16 + 0) by reflexivity. apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  apply seao_nil.
Qed.