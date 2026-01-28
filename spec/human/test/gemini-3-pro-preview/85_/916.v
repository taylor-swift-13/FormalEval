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

Example test_case : problem_85_spec [65%Z; 3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 122%Z; 6%Z; 8%Z; 10%Z; 556%Z; 100%Z; 187%Z; 920%Z; 26%Z; 37%Z; 29%Z] 1038%Z.
Proof.
  unfold problem_85_spec.
  (* Idx 0: 65. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 1: 3. Odd, but 3 not even. *)
  apply seao_other. right; reflexivity.
  (* Idx 2: 5. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 3: 7. Odd, but 7 not even. *)
  apply seao_other. right; reflexivity.
  (* Idx 4: 9. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 5: 2. Odd, 2 even. Add 2. *)
  replace 1038 with (2 + 1036) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Idx 6: 122. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 7: 6. Odd, 6 even. Add 6. *)
  replace 1036 with (6 + 1030) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Idx 8: 8. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 9: 10. Odd, 10 even. Add 10. *)
  replace 1030 with (10 + 1020) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Idx 10: 556. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 11: 100. Odd, 100 even. Add 100. *)
  replace 1020 with (100 + 920) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Idx 12: 187. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 13: 920. Odd, 920 even. Add 920. *)
  replace 920 with (920 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Idx 14: 26. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 15: 37. Odd, 37 not even. *)
  apply seao_other. right; reflexivity.
  (* Idx 16: 29. Not odd. *)
  apply seao_other. left; reflexivity.
  (* Idx 17: nil. *)
  apply seao_nil.
Qed.