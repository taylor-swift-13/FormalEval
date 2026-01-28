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

Example test_case : problem_85_spec [2%Z; 4%Z; 6%Z; 88%Z; 10%Z; 12%Z; 14%Z; 16%Z; 15%Z; 20%Z; 22%Z; 24%Z; 28%Z; 30%Z; 16%Z; 16%Z; 24%Z] 210%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. reflexivity.
  change 210 with (4 + 206). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  change 206 with (88 + 118). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  change 118 with (12 + 106). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  change 106 with (16 + 90). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  change 90 with (20 + 70). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  change 70 with (24 + 46). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  change 46 with (30 + 16). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  change 16 with (16 + 0). apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_nil.
Qed.