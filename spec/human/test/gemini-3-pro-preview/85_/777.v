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

Example test_case : problem_85_spec [2%Z; 4%Z; 8%Z; 10%Z; 12%Z; 16%Z; 14%Z; 18%Z; 101%Z; 22%Z; 24%Z; 26%Z; 28%Z; 30%Z; 30%Z; 16%Z; 22%Z] 142%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. simpl. reflexivity.
  replace 142%Z with (4 + 138)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  replace 138%Z with (10 + 128)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  replace 128%Z with (16 + 112)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  replace 112%Z with (18 + 94)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  replace 94%Z with (22 + 72)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  replace 72%Z with (26 + 46)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  replace 46%Z with (30 + 16)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  replace 16%Z with (16 + 0)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  apply seao_other. left. simpl. reflexivity.
  apply seao_nil.
Qed.