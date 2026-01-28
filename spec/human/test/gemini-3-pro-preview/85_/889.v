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

Example test_case : problem_85_spec [3; 33; 5; 7; 9; 122; 6; 19; 7; 10; 556; 100; 187; 920; 42; 37; 29; 10]%Z 1162%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 1162 with (122 + 1040) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 1040 with (10 + 1030) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 1030 with (100 + 930) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 930 with (920 + 10) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  replace 10 with (10 + 0) by reflexivity. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_nil.
Qed.