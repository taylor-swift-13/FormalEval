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

Example test_case : problem_85_spec [2%Z; 4%Z; 6%Z; 17%Z; 10%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z; 17%Z; 24%Z; 13%Z; 28%Z; 30%Z; 6%Z; 4%Z] 118%Z.
Proof.
  unfold problem_85_spec.
  (* i=0, v=2: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=1, v=4: odd index, even val. 118 = 4 + 114 *)
  replace 118 with (4 + 114) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=2, v=6: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=3, v=17: odd index, odd val *)
  apply seao_other; [right; reflexivity | ].
  (* i=4, v=10: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=5, v=8: odd index, even val. 114 = 8 + 106 *)
  replace 114 with (8 + 106) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=6, v=10: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=7, v=12: odd index, even val. 106 = 12 + 94 *)
  replace 106 with (12 + 94) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=8, v=14: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=9, v=16: odd index, even val. 94 = 16 + 78 *)
  replace 94 with (16 + 78) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=10, v=18: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=11, v=20: odd index, even val. 78 = 20 + 58 *)
  replace 78 with (20 + 58) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=12, v=17: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=13, v=24: odd index, even val. 58 = 24 + 34 *)
  replace 58 with (24 + 34) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=14, v=13: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=15, v=28: odd index, even val. 34 = 28 + 6 *)
  replace 34 with (28 + 6) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=16, v=30: even index *)
  apply seao_other; [left; reflexivity | ].
  (* i=17, v=6: odd index, even val. 6 = 6 + 0 *)
  replace 6 with (6 + 0) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* i=18, v=4: even index *)
  apply seao_other; [left; reflexivity | ].
  (* nil *)
  apply seao_nil.
Qed.