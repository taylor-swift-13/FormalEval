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

Example test_case : problem_85_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 6%Z; 8%Z; 10%Z; 556%Z; 100%Z; 920%Z; 42%Z; 37%Z; 27%Z; 7%Z; 8%Z; 187%Z; 37%Z] 166%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 1: 5. Odd index, Odd value. *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 2: 7. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 3: 9. Odd index, Odd value. *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 4: 2. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 5: 6. Odd index, Even value. Add 6. Remaining: 160. *)
  replace 166 with (6 + 160) by reflexivity.
  apply seao_odd_even; try (simpl; reflexivity).
  (* Index 6: 8. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 7: 10. Odd index, Even value. Add 10. Remaining: 150. *)
  replace 160 with (10 + 150) by reflexivity.
  apply seao_odd_even; try (simpl; reflexivity).
  (* Index 8: 556. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 9: 100. Odd index, Even value. Add 100. Remaining: 50. *)
  replace 150 with (100 + 50) by reflexivity.
  apply seao_odd_even; try (simpl; reflexivity).
  (* Index 10: 920. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 11: 42. Odd index, Even value. Add 42. Remaining: 8. *)
  replace 50 with (42 + 8) by reflexivity.
  apply seao_odd_even; try (simpl; reflexivity).
  (* Index 12: 37. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 13: 27. Odd index, Odd value. *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 14: 7. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 15: 8. Odd index, Even value. Add 8. Remaining: 0. *)
  replace 8 with (8 + 0) by reflexivity.
  apply seao_odd_even; try (simpl; reflexivity).
  (* Index 16: 187. Even index. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 17: 37. Odd index, Odd value. *)
  apply seao_other. right. simpl. reflexivity.
  (* End of list *)
  apply seao_nil.
Qed.