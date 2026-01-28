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

Example test_case : problem_85_spec [2; 4; 6; 8; 10; 12; 14; 16; 18; 20; 22; 24; 26; 28; 30; 30; 16] 142.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. reflexivity.
  replace 142 with (4 + 138) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 138 with (8 + 130) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 130 with (12 + 118) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 118 with (16 + 102) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 102 with (20 + 82) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 82 with (24 + 58) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 58 with (28 + 30) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  replace 30 with (30 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_nil.
Qed.