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

Example test_case : problem_85_spec [55; 3; 1; 2; 3; 4; 5; 6; 7; 17; 8; 9; 10; 10; 11; 13; 14; 15; 16; 99; 18; 19; 20; 3; 3; 99] 22%Z.
Proof.
  unfold problem_85_spec.
  (* 0: 55 *) apply seao_other; [left; reflexivity | ].
  (* 1: 3 *) apply seao_other; [right; reflexivity | ].
  (* 2: 1 *) apply seao_other; [left; reflexivity | ].
  (* 3: 2 *) replace 22%Z with (2 + 20)%Z by reflexivity; apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 4: 3 *) apply seao_other; [left; reflexivity | ].
  (* 5: 4 *) replace 20%Z with (4 + 16)%Z by reflexivity; apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 6: 5 *) apply seao_other; [left; reflexivity | ].
  (* 7: 6 *) replace 16%Z with (6 + 10)%Z by reflexivity; apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 8: 7 *) apply seao_other; [left; reflexivity | ].
  (* 9: 17 *) apply seao_other; [right; reflexivity | ].
  (* 10: 8 *) apply seao_other; [left; reflexivity | ].
  (* 11: 9 *) apply seao_other; [right; reflexivity | ].
  (* 12: 10 *) apply seao_other; [left; reflexivity | ].
  (* 13: 10 *) replace 10%Z with (10 + 0)%Z by reflexivity; apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 14: 11 *) apply seao_other; [left; reflexivity | ].
  (* 15: 13 *) apply seao_other; [right; reflexivity | ].
  (* 16: 14 *) apply seao_other; [left; reflexivity | ].
  (* 17: 15 *) apply seao_other; [right; reflexivity | ].
  (* 18: 16 *) apply seao_other; [left; reflexivity | ].
  (* 19: 99 *) apply seao_other; [right; reflexivity | ].
  (* 20: 18 *) apply seao_other; [left; reflexivity | ].
  (* 21: 19 *) apply seao_other; [right; reflexivity | ].
  (* 22: 20 *) apply seao_other; [left; reflexivity | ].
  (* 23: 3 *) apply seao_other; [right; reflexivity | ].
  (* 24: 3 *) apply seao_other; [left; reflexivity | ].
  (* 25: 99 *) apply seao_other; [right; reflexivity | ].
  apply seao_nil.
Qed.