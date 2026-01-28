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

Example test_case : problem_85_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 10%Z; 17%Z; 4%Z] 110%Z.
Proof.
  unfold problem_85_spec.
  (* i=0, h=1. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=1, h=2. Odd index, Even val. Add. *)
  replace 110 with (2 + 108) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=2, h=3. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=3, h=4. Odd index, Even val. Add. *)
  replace 108 with (4 + 104) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=4, h=5. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=5, h=6. Odd index, Even val. Add. *)
  replace 104 with (6 + 98) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=6, h=7. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=7, h=8. Odd index, Even val. Add. *)
  replace 98 with (8 + 90) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=8, h=9. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=9, h=10. Odd index, Even val. Add. *)
  replace 90 with (10 + 80) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=10, h=11. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=11, h=12. Odd index, Even val. Add. *)
  replace 80 with (12 + 68) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=12, h=13. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=13, h=14. Odd index, Even val. Add. *)
  replace 68 with (14 + 54) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=14, h=15. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=15, h=16. Odd index, Even val. Add. *)
  replace 54 with (16 + 38) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=16, h=17. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=17, h=18. Odd index, Even val. Add. *)
  replace 38 with (18 + 20) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=18, h=19. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=19, h=20. Odd index, Even val. Add. *)
  replace 20 with (20 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=20, h=10. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=21, h=17. Odd index, Odd val. Skip. *)
  apply seao_other. right; reflexivity.
  (* i=22, h=4. Even index. Skip. *)
  apply seao_other. left; reflexivity.
  (* i=23, nil. *)
  apply seao_nil.
Qed.