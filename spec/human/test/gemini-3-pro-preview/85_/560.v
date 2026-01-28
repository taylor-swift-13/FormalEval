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

Example test_case : problem_85_spec [1; 2; 3; 4; 5; 6; 7; 8; 9; 6; 10; 11; 12; 12; 13; 14; 15; 16; 17; 18; 33; 20; 10; 8; 13]%Z 114%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other; [left; reflexivity |].
  replace 114 with (2 + 112) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 112 with (4 + 108) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 108 with (6 + 102) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 102 with (8 + 94) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 94 with (6 + 88) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  apply seao_other; [right; reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 88 with (12 + 76) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 76 with (14 + 62) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 62 with (16 + 46) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 46 with (18 + 28) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 28 with (20 + 8) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  replace 8 with (8 + 0) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity |].
  apply seao_other; [left; reflexivity |].
  apply seao_nil.
Qed.