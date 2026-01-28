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

Example test_case : problem_85_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 18%Z; 19%Z; 20%Z; 10%Z] 110%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 1: 2. Odd index, even value. *)
  replace 110%Z with (2 + 108)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 2: 3. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 3: 4. Odd index, even value. *)
  replace 108%Z with (4 + 104)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 4: 5. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 5: 6. Odd index, even value. *)
  replace 104%Z with (6 + 98)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 6: 7. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 7: 8. Odd index, even value. *)
  replace 98%Z with (8 + 90)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 8: 9. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 9: 10. Odd index, even value. *)
  replace 90%Z with (10 + 80)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 10: 11. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 11: 12. Odd index, even value. *)
  replace 80%Z with (12 + 68)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 12: 13. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 13: 14. Odd index, even value. *)
  replace 68%Z with (14 + 54)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 14: 15. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 15: 16. Odd index, even value. *)
  replace 54%Z with (16 + 38)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 16: 17. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 17: 18. Odd index, even value. *)
  replace 38%Z with (18 + 20)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 18: 19. Even index. *)
  apply seao_other. left. reflexivity.
  (* Index 19: 20. Odd index, even value. *)
  replace 20%Z with (20 + 0)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 20: 10. Even index. *)
  apply seao_other. left. reflexivity.
  (* Nil *)
  apply seao_nil.
Qed.