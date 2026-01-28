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

Example test_case : problem_85_spec [3%Z; 2%Z; 557%Z; 4%Z; 5%Z; 6%Z; 7%Z; 17%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 17%Z; 15%Z; 16%Z; 9%Z; 17%Z; 18%Z; 20%Z; 20%Z; 15%Z] 48%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 1: 2 (odd index, even val -> add) *)
  replace 48 with (2 + 46) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 2: 557 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 3: 4 (odd index, even val -> add) *)
  replace 46 with (4 + 42) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 4: 5 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 5: 6 (odd index, even val -> add) *)
  replace 42 with (6 + 36) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 6: 7 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 7: 17 (odd index, odd val -> skip) *)
  apply seao_other. right. reflexivity.
  (* Index 8: 8 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 9: 9 (odd index, odd val -> skip) *)
  apply seao_other. right. reflexivity.
  (* Index 10: 10 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 11: 11 (odd index, odd val -> skip) *)
  apply seao_other. right. reflexivity.
  (* Index 12: 12 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 13: 17 (odd index, odd val -> skip) *)
  apply seao_other. right. reflexivity.
  (* Index 14: 15 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 15: 16 (odd index, even val -> add) *)
  replace 36 with (16 + 20) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 16: 9 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 17: 17 (odd index, odd val -> skip) *)
  apply seao_other. right. reflexivity.
  (* Index 18: 18 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 19: 20 (odd index, even val -> add) *)
  replace 20 with (20 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 20: 20 (even index -> skip) *)
  apply seao_other. left. reflexivity.
  (* Index 21: 15 (odd index, odd val -> skip) *)
  apply seao_other. right. reflexivity.
  (* Index 22: nil *)
  apply seao_nil.
Qed.