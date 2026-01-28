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

Example test_case : problem_85_spec [2%Z; 4%Z; 6%Z; 42%Z; 8%Z; 10%Z; 14%Z; 16%Z; 18%Z; 20%Z; 22%Z; 24%Z; 26%Z; 28%Z; 30%Z; 28%Z; 14%Z; 4%Z] 176%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 2. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 1: 4. Odd index, even value -> seao_odd_even *)
  replace 176%Z with (4 + 172)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 2: 6. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 3: 42. Odd index, even value -> seao_odd_even *)
  replace 172%Z with (42 + 130)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 4: 8. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 5: 10. Odd index, even value -> seao_odd_even *)
  replace 130%Z with (10 + 120)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 14. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 7: 16. Odd index, even value -> seao_odd_even *)
  replace 120%Z with (16 + 104)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 8: 18. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 9: 20. Odd index, even value -> seao_odd_even *)
  replace 104%Z with (20 + 84)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 10: 22. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 11: 24. Odd index, even value -> seao_odd_even *)
  replace 84%Z with (24 + 60)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 12: 26. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 13: 28. Odd index, even value -> seao_odd_even *)
  replace 60%Z with (28 + 32)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 14: 30. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 15: 28. Odd index, even value -> seao_odd_even *)
  replace 32%Z with (28 + 4)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 16: 14. Even index -> seao_other *)
  apply seao_other; [left; reflexivity | ].
  (* Index 17: 4. Odd index, even value -> seao_odd_even *)
  replace 4%Z with (4 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* End of list *)
  apply seao_nil.
Qed.