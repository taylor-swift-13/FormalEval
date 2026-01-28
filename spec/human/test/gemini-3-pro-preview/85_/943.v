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

Example test_case : problem_85_spec [3%Z; 6%Z; 24%Z; 7%Z; 4%Z; 8%Z; 1%Z; 10%Z; 10%Z; 4%Z] 28%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3. Even index -> skip *)
  apply seao_other. left. reflexivity.
  (* Index 1: 6. Odd index, even value -> add 6. Remaining sum 22. *)
  replace 28%Z with (6 + 22)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 2: 24. Even index -> skip *)
  apply seao_other. left. reflexivity.
  (* Index 3: 7. Odd index, odd value -> skip *)
  apply seao_other. right. reflexivity.
  (* Index 4: 4. Even index -> skip *)
  apply seao_other. left. reflexivity.
  (* Index 5: 8. Odd index, even value -> add 8. Remaining sum 14. *)
  replace 22%Z with (8 + 14)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 1. Even index -> skip *)
  apply seao_other. left. reflexivity.
  (* Index 7: 10. Odd index, even value -> add 10. Remaining sum 4. *)
  replace 14%Z with (10 + 4)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 8: 10. Even index -> skip *)
  apply seao_other. left. reflexivity.
  (* Index 9: 4. Odd index, even value -> add 4. Remaining sum 0. *)
  replace 4%Z with (4 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 10: []. End. *)
  apply seao_nil.
Qed.