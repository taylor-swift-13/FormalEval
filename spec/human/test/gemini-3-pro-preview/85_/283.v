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

Example test_case : problem_85_spec [3%Z; 1%Z; 101%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 17%Z; 8%Z; 14%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 10%Z; 16%Z] 114%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  apply seao_other; [right; reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 114%Z with (8 + 106)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 106%Z with (10 + 96)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 96%Z with (12 + 84)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 84%Z with (14 + 70)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 70%Z with (16 + 54)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 54%Z with (18 + 36)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 36%Z with (20 + 16)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_other; [left; reflexivity | ].
  change 16%Z with (16 + 0)%Z. apply seao_odd_even; [reflexivity | reflexivity | ].
  apply seao_nil.
Qed.