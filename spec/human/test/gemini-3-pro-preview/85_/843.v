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

Example test_case : problem_85_spec [22%Z; 44%Z; 55%Z; 66%Z; 77%Z; 100%Z; 88%Z; 99%Z; 44%Z; 22%Z; 37%Z] 232%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 22. Even index. *)
  apply seao_other; [ left; simpl; reflexivity | ].
  (* Index 1: 44. Odd index, Even value. *)
  replace 232%Z with (44 + 188)%Z by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  (* Index 2: 55. Even index. *)
  apply seao_other; [ left; simpl; reflexivity | ].
  (* Index 3: 66. Odd index, Even value. *)
  replace 188%Z with (66 + 122)%Z by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  (* Index 4: 77. Even index. *)
  apply seao_other; [ left; simpl; reflexivity | ].
  (* Index 5: 100. Odd index, Even value. *)
  replace 122%Z with (100 + 22)%Z by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  (* Index 6: 88. Even index. *)
  apply seao_other; [ left; simpl; reflexivity | ].
  (* Index 7: 99. Odd index, Odd value. *)
  apply seao_other; [ right; simpl; reflexivity | ].
  (* Index 8: 44. Even index. *)
  apply seao_other; [ left; simpl; reflexivity | ].
  (* Index 9: 22. Odd index, Even value. *)
  replace 22%Z with (22 + 0)%Z by reflexivity.
  apply seao_odd_even; [ simpl; reflexivity | simpl; reflexivity | ].
  (* Index 10: 37. Even index. *)
  apply seao_other; [ left; simpl; reflexivity | ].
  (* Index 11: Nil. *)
  apply seao_nil.
Qed.