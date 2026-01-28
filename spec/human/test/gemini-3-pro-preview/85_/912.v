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

Example test_case : problem_85_spec [3%Z; 556%Z; 2%Z; 7%Z; 8%Z; 9%Z; 31%Z; 10%Z; 3%Z; 556%Z] 1122%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3. Not odd index. *)
  apply seao_other. left; reflexivity.
  (* Index 1: 556. Odd index, even value. Add 556. *)
  replace 1122 with (556 + 566) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 2: 2. Not odd index. *)
  apply seao_other. left; reflexivity.
  (* Index 3: 7. Odd index, not even value. *)
  apply seao_other. right; reflexivity.
  (* Index 4: 8. Not odd index. *)
  apply seao_other. left; reflexivity.
  (* Index 5: 9. Odd index, not even value. *)
  apply seao_other. right; reflexivity.
  (* Index 6: 31. Not odd index. *)
  apply seao_other. left; reflexivity.
  (* Index 7: 10. Odd index, even value. Add 10. *)
  replace 566 with (10 + 556) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 8: 3. Not odd index. *)
  apply seao_other. left; reflexivity.
  (* Index 9: 556. Odd index, even value. Add 556. *)
  replace 556 with (556 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 10: Nil. *)
  apply seao_nil.
Qed.