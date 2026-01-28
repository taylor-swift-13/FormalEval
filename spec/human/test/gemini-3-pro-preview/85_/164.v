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

Example test_case : problem_85_spec [2; 4; 6; 13; 8; 10; 12; 14; 16; 18; 20; 22; 24; 26; 28; 30] 124.
Proof.
  unfold problem_85_spec.
  (* i=0, 2: even index *)
  apply seao_other. left; reflexivity.
  (* i=1, 4: odd index, even val *)
  replace 124 with (4 + 120) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=2, 6: even index *)
  apply seao_other. left; reflexivity.
  (* i=3, 13: odd index, odd val *)
  apply seao_other. right; reflexivity.
  (* i=4, 8: even index *)
  apply seao_other. left; reflexivity.
  (* i=5, 10: odd index, even val *)
  replace 120 with (10 + 110) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=6, 12: even index *)
  apply seao_other. left; reflexivity.
  (* i=7, 14: odd index, even val *)
  replace 110 with (14 + 96) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=8, 16: even index *)
  apply seao_other. left; reflexivity.
  (* i=9, 18: odd index, even val *)
  replace 96 with (18 + 78) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=10, 20: even index *)
  apply seao_other. left; reflexivity.
  (* i=11, 22: odd index, even val *)
  replace 78 with (22 + 56) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=12, 24: even index *)
  apply seao_other. left; reflexivity.
  (* i=13, 26: odd index, even val *)
  replace 56 with (26 + 30) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=14, 28: even index *)
  apply seao_other. left; reflexivity.
  (* i=15, 30: odd index, even val *)
  replace 30 with (30 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=16, nil *)
  apply seao_nil.
Qed.