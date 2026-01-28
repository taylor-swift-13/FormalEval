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

Example test_case : problem_85_spec [8%Z; 122%Z; 9%Z; 4%Z; 6%Z; 10%Z; 13%Z; 15%Z; 9%Z] 136%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 8. i=0 not odd. *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 1: 122. i=1 odd, 122 even. Sum += 122. *)
  replace 136 with (122 + 14) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 2: 9. i=2 not odd. *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 3: 4. i=3 odd, 4 even. Sum += 4. *)
  replace 14 with (4 + 10) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 4: 6. i=4 not odd. *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 5: 10. i=5 odd, 10 even. Sum += 10. *)
  replace 10 with (10 + 0) by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 6: 13. i=6 not odd. *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* Index 7: 15. i=7 odd, 15 not even. *)
  apply seao_other; [right; simpl; reflexivity | ].
  (* Index 8: 9. i=8 not odd. *)
  apply seao_other; [left; simpl; reflexivity | ].
  (* End of list. *)
  apply seao_nil.
Qed.