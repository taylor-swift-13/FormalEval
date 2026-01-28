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

Example test_case : problem_85_spec [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 42; 13; 14; 15; 17; 18; 19; 10; 17]%Z 76%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other; [left; reflexivity | ].
  replace 76%Z with (2 + 74)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 74%Z with (4 + 70)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 70%Z with (6 + 64)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 64%Z with (8 + 56)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 56%Z with (42 + 14)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 14%Z with (14 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_nil.
Qed.