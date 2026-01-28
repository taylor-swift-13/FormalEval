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

Example test_case : problem_85_spec [11%Z; 8%Z; 66%Z; 67%Z; 77%Z; 88%Z; 99%Z; 100%Z; 77%Z; 76%Z; 100%Z; 66%Z; 100%Z; 66%Z] 404%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 1: 8. Odd index, Even value. *)
  replace 404%Z with (8 + 396)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Index 2: 66. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 3: 67. Odd index, Odd value. *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 4: 77. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 5: 88. Odd index, Even value. *)
  replace 396%Z with (88 + 308)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Index 6: 99. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 7: 100. Odd index, Even value. *)
  replace 308%Z with (100 + 208)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Index 8: 77. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 9: 76. Odd index, Even value. *)
  replace 208%Z with (76 + 132)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Index 10: 100. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 11: 66. Odd index, Even value. *)
  replace 132%Z with (66 + 66)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Index 12: 100. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 13: 66. Odd index, Even value. *)
  replace 66%Z with (66 + 0)%Z by reflexivity.
  apply seao_odd_even. simpl. reflexivity. simpl. reflexivity.
  (* Nil *)
  apply seao_nil.
Qed.