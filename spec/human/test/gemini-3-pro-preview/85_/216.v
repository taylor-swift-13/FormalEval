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

Example test_case : problem_85_spec [3; 2; 3; 4; 5; 6; 7; 17; 8; 9; 10; 11; 12; 17; 14; 15; 16; 9; 17; 18; 20; 20; 15]%Z 50%Z.
Proof.
  unfold problem_85_spec.
  (* 0: 3 *)
  apply seao_other. left; reflexivity.
  (* 1: 2 *)
  replace 50 with (2 + 48) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* 2: 3 *)
  apply seao_other. left; reflexivity.
  (* 3: 4 *)
  replace 48 with (4 + 44) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* 4: 5 *)
  apply seao_other. left; reflexivity.
  (* 5: 6 *)
  replace 44 with (6 + 38) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* 6: 7 *)
  apply seao_other. left; reflexivity.
  (* 7: 17 *)
  apply seao_other. right; reflexivity.
  (* 8: 8 *)
  apply seao_other. left; reflexivity.
  (* 9: 9 *)
  apply seao_other. right; reflexivity.
  (* 10: 10 *)
  apply seao_other. left; reflexivity.
  (* 11: 11 *)
  apply seao_other. right; reflexivity.
  (* 12: 12 *)
  apply seao_other. left; reflexivity.
  (* 13: 17 *)
  apply seao_other. right; reflexivity.
  (* 14: 14 *)
  apply seao_other. left; reflexivity.
  (* 15: 15 *)
  apply seao_other. right; reflexivity.
  (* 16: 16 *)
  apply seao_other. left; reflexivity.
  (* 17: 9 *)
  apply seao_other. right; reflexivity.
  (* 18: 17 *)
  apply seao_other. left; reflexivity.
  (* 19: 18 *)
  replace 38 with (18 + 20) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* 20: 20 *)
  apply seao_other. left; reflexivity.
  (* 21: 20 *)
  replace 20 with (20 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* 22: 15 *)
  apply seao_other. left; reflexivity.
  (* nil *)
  apply seao_nil.
Qed.