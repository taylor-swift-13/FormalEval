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

Example test_case : problem_85_spec [3; 5; 7; 9; 2; 6; 8; 10; 556; 100; 187; 920; 42; 37; 29; 7; 8; 187] 1036%Z.
Proof.
  unfold problem_85_spec.
  (* 0: 3 *)
  apply seao_other; [left; reflexivity |].
  (* 1: 5 *)
  apply seao_other; [right; reflexivity |].
  (* 2: 7 *)
  apply seao_other; [left; reflexivity |].
  (* 3: 9 *)
  apply seao_other; [right; reflexivity |].
  (* 4: 2 *)
  apply seao_other; [left; reflexivity |].
  (* 5: 6 (add 6) *)
  replace 1036%Z with (6 + 1030)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* 6: 8 *)
  apply seao_other; [left; reflexivity |].
  (* 7: 10 (add 10) *)
  replace 1030%Z with (10 + 1020)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* 8: 556 *)
  apply seao_other; [left; reflexivity |].
  (* 9: 100 (add 100) *)
  replace 1020%Z with (100 + 920)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* 10: 187 *)
  apply seao_other; [left; reflexivity |].
  (* 11: 920 (add 920) *)
  replace 920%Z with (920 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* 12: 42 *)
  apply seao_other; [left; reflexivity |].
  (* 13: 37 *)
  apply seao_other; [right; reflexivity |].
  (* 14: 29 *)
  apply seao_other; [left; reflexivity |].
  (* 15: 7 *)
  apply seao_other; [right; reflexivity |].
  (* 16: 8 *)
  apply seao_other; [left; reflexivity |].
  (* 17: 187 *)
  apply seao_other; [right; reflexivity |].
  (* Nil *)
  apply seao_nil.
Qed.