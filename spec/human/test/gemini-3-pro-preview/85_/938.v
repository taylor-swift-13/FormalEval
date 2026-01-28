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

Example test_case : problem_85_spec [11%Z; 11%Z; 22%Z; 33%Z; 66%Z; 66%Z; 77%Z; 68%Z; 88%Z; 99%Z; 101%Z] 134%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 1: 11. Odd index, odd value. *)
  apply seao_other. right. reflexivity.
  (* Index 2: 22. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 3: 33. Odd index, odd value. *)
  apply seao_other. right. reflexivity.
  (* Index 4: 66. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 5: 66. Odd index, even value. Sum adds 66. Remaining sum needed: 68. *)
  replace 134%Z with (66 + 68)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 6: 77. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 7: 68. Odd index, even value. Sum adds 68. Remaining sum needed: 0. *)
  replace 68%Z with (68 + 0)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 8: 88. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 9: 99. Odd index, odd value. *)
  apply seao_other. right. reflexivity.
  (* Index 10: 101. Even index. *)
  apply seao_other. left. reflexivity.
  (* End of list *)
  apply seao_nil.
Qed.