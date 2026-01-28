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

Example test_case : problem_85_spec [8%Z; 1%Z; 5%Z; 6%Z; 3%Z; 8%Z; 7%Z; 6%Z; 9%Z; 2%Z; 8%Z] 22%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 8. Nat.odd 0 = false. Use seao_other (left). *)
  apply seao_other. left. reflexivity.
  (* Index 1: 1. Nat.odd 1 = true, Z.even 1 = false. Use seao_other (right). *)
  apply seao_other. right. reflexivity.
  (* Index 2: 5. Nat.odd 2 = false. Use seao_other (left). *)
  apply seao_other. left. reflexivity.
  (* Index 3: 6. Nat.odd 3 = true, Z.even 6 = true. Use seao_odd_even. *)
  replace 22 with (6 + 16) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 4: 3. Nat.odd 4 = false. Use seao_other (left). *)
  apply seao_other. left. reflexivity.
  (* Index 5: 8. Nat.odd 5 = true, Z.even 8 = true. Use seao_odd_even. *)
  replace 16 with (8 + 8) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 6: 7. Nat.odd 6 = false. Use seao_other (left). *)
  apply seao_other. left. reflexivity.
  (* Index 7: 6. Nat.odd 7 = true, Z.even 6 = true. Use seao_odd_even. *)
  replace 8 with (6 + 2) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 8: 9. Nat.odd 8 = false. Use seao_other (left). *)
  apply seao_other. left. reflexivity.
  (* Index 9: 2. Nat.odd 9 = true, Z.even 2 = true. Use seao_odd_even. *)
  replace 2 with (2 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 10: 8. Nat.odd 10 = false. Use seao_other (left). *)
  apply seao_other. left. reflexivity.
  (* Nil *)
  apply seao_nil.
Qed.