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

Example test_case : problem_85_spec [3%Z; 8%Z; 2%Z; 557%Z; 4%Z; 5%Z; 6%Z; 43%Z; 17%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 17%Z; 15%Z; 16%Z; 10%Z; 17%Z; 18%Z; 20%Z; 20%Z; 15%Z] 86%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. simpl; reflexivity.
  replace 86%Z with (8 + 78)%Z by reflexivity. apply seao_odd_even; try (simpl; reflexivity).
  apply seao_other. left. simpl; reflexivity.
  apply seao_other. right. simpl; reflexivity.
  apply seao_other. left. simpl; reflexivity.
  apply seao_other. right. simpl; reflexivity.
  apply seao_other. left. simpl; reflexivity.
  apply seao_other. right. simpl; reflexivity.
  apply seao_other. left. simpl; reflexivity.
  replace 78%Z with (8 + 70)%Z by reflexivity. apply seao_odd_even; try (simpl; reflexivity).
  apply seao_other. left. simpl; reflexivity.
  replace 70%Z with (10 + 60)%Z by reflexivity. apply seao_odd_even; try (simpl; reflexivity).
  apply seao_other. left. simpl; reflexivity.
  replace 60%Z with (12 + 48)%Z by reflexivity. apply seao_odd_even; try (simpl; reflexivity).
  apply seao_other. left. simpl; reflexivity.
  apply seao_other. right. simpl; reflexivity.
  apply seao_other. left. simpl; reflexivity.
  replace 48%Z with (10 + 38)%Z by reflexivity. apply seao_odd_even; try (simpl; reflexivity).
  apply seao_other. left. simpl; reflexivity.
  replace 38%Z with (18 + 20)%Z by reflexivity. apply seao_odd_even; try (simpl; reflexivity).
  apply seao_other. left. simpl; reflexivity.
  replace 20%Z with (20 + 0)%Z by reflexivity. apply seao_odd_even; try (simpl; reflexivity).
  apply seao_other. left. simpl; reflexivity.
  apply seao_nil.
Qed.