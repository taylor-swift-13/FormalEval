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

Example test_case : problem_85_spec [2%Z; 6%Z; 11%Z; 17%Z; 8%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z; 17%Z; 24%Z; 13%Z; 28%Z; 30%Z; 6%Z] 120%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 2 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 1: 6 (Odd index, Even value) *)
  replace 120%Z with (6 + 114)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 2: 11 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 3: 17 (Odd index, Odd value) *)
  apply seao_other; [right; simpl; reflexivity | ].
  (* Index 4: 8 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 5: 8 (Odd index, Even value) *)
  replace 114%Z with (8 + 106)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 6: 10 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 7: 12 (Odd index, Even value) *)
  replace 106%Z with (12 + 94)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 8: 14 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 9: 16 (Odd index, Even value) *)
  replace 94%Z with (16 + 78)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 10: 18 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 11: 20 (Odd index, Even value) *)
  replace 78%Z with (20 + 58)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 12: 17 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 13: 24 (Odd index, Even value) *)
  replace 58%Z with (24 + 34)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 14: 13 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 15: 28 (Odd index, Even value) *)
  replace 34%Z with (28 + 6)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 16: 30 (Even index) *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 17: 6 (Odd index, Even value) *)
  replace 6%Z with (6 + 0)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 18: Nil *)
  apply seao_nil.
Qed.