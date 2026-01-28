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

Example test_case : problem_85_spec [2%Z; 7%Z; 17%Z; 10%Z; 8%Z; 10%Z; 12%Z; 14%Z; 42%Z; 18%Z; 20%Z; 17%Z; 24%Z; 26%Z; 28%Z; 30%Z; 17%Z] 108%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 2 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 1: 7 (odd index, odd value) *)
  apply seao_other. right. reflexivity.
  (* Index 2: 17 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 3: 10 (odd index, even value) -> add 10 *)
  replace 108%Z with (10 + 98)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 4: 8 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 5: 10 (odd index, even value) -> add 10 *)
  replace 98%Z with (10 + 88)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 6: 12 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 7: 14 (odd index, even value) -> add 14 *)
  replace 88%Z with (14 + 74)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 8: 42 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 9: 18 (odd index, even value) -> add 18 *)
  replace 74%Z with (18 + 56)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 10: 20 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 11: 17 (odd index, odd value) *)
  apply seao_other. right. reflexivity.
  (* Index 12: 24 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 13: 26 (odd index, even value) -> add 26 *)
  replace 56%Z with (26 + 30)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 14: 28 (even index) *)
  apply seao_other. left. reflexivity.
  (* Index 15: 30 (odd index, even value) -> add 30 *)
  replace 30%Z with (30 + 0)%Z by reflexivity.
  apply seao_odd_even; try reflexivity.
  (* Index 16: 17 (even index) *)
  apply seao_other. left. reflexivity.
  (* End of list *)
  apply seao_nil.
Qed.