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

Example test_case : problem_85_spec [187%Z; 1%Z; 2%Z; 3%Z; 4%Z; 24%Z; 5%Z; 42%Z; 7%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 37%Z; 3%Z; 2%Z; 5%Z; 20%Z; 18%Z] 88%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  replace 88%Z with (24 + 64)%Z by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other. left. reflexivity.
  replace 64%Z with (42 + 22)%Z by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  apply seao_other. right. reflexivity.
  apply seao_other. left. reflexivity.
  replace 22%Z with (2 + 20)%Z by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other. left. reflexivity.
  replace 20%Z with (20 + 0)%Z by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other. left. reflexivity.
  apply seao_nil.
Qed.