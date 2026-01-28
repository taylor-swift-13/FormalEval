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

Example test_case : problem_85_spec [1%Z; 5%Z; 8%Z; 8%Z; 10%Z; 6%Z; 9%Z; 23%Z; 2%Z; 7%Z] 14%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0, Val 1: not odd index *)
  apply seao_other. left. reflexivity.
  (* Index 1, Val 5: odd index, not even val *)
  apply seao_other. right. reflexivity.
  (* Index 2, Val 8: not odd index *)
  apply seao_other. left. reflexivity.
  (* Index 3, Val 8: odd index, even val. 14 = 8 + 6 *)
  replace 14%Z with (8 + 6)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 4, Val 10: not odd index *)
  apply seao_other. left. reflexivity.
  (* Index 5, Val 6: odd index, even val. 6 = 6 + 0 *)
  replace 6%Z with (6 + 0)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 6, Val 9: not odd index *)
  apply seao_other. left. reflexivity.
  (* Index 7, Val 23: odd index, not even val *)
  apply seao_other. right. reflexivity.
  (* Index 8, Val 2: not odd index *)
  apply seao_other. left. reflexivity.
  (* Index 9, Val 7: odd index, not even val *)
  apply seao_other. right. reflexivity.
  (* Nil *)
  apply seao_nil.
Qed.