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

Example test_case : problem_85_spec [3; 1; 2; 3; 4; 5; 6; 7; 17; 8; 9; 10; 11; 12; 17; 14; 15; 16; 9; 17; 20; 20; 15]%Z 80%Z.
Proof.
  unfold problem_85_spec.
  (* 0: 3 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 1: 1 (Skip: odd value) *)
  apply seao_other; [right; reflexivity | ].
  (* 2: 2 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 3: 3 (Skip: odd value) *)
  apply seao_other; [right; reflexivity | ].
  (* 4: 4 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 5: 5 (Skip: odd value) *)
  apply seao_other; [right; reflexivity | ].
  (* 6: 6 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 7: 7 (Skip: odd value) *)
  apply seao_other; [right; reflexivity | ].
  (* 8: 17 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 9: 8 (Add: odd index, even value). Sum: 80 = 8 + 72 *)
  replace 80 with (8 + 72) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 10: 9 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 11: 10 (Add: odd index, even value). Sum: 72 = 10 + 62 *)
  replace 72 with (10 + 62) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 12: 11 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 13: 12 (Add: odd index, even value). Sum: 62 = 12 + 50 *)
  replace 62 with (12 + 50) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 14: 17 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 15: 14 (Add: odd index, even value). Sum: 50 = 14 + 36 *)
  replace 50 with (14 + 36) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 16: 15 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 17: 16 (Add: odd index, even value). Sum: 36 = 16 + 20 *)
  replace 36 with (16 + 20) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 18: 9 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 19: 17 (Skip: odd value) *)
  apply seao_other; [right; reflexivity | ].
  (* 20: 20 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* 21: 20 (Add: odd index, even value). Sum: 20 = 20 + 0 *)
  replace 20 with (20 + 0) by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* 22: 15 (Skip: even index) *)
  apply seao_other; [left; reflexivity | ].
  (* Nil *)
  apply seao_nil.
Qed.