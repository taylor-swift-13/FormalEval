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

Example test_case : problem_85_spec [3; 6; 7; 4; 8; 1; 8; 10; 5; 10; 5; 3]%Z 30%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3 (odd index: false) -> skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 1: 6 (odd index: true, even val: true) -> add 6 *)
  replace 30%Z with (6 + 24)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 2: 7 (odd index: false) -> skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 3: 4 (odd index: true, even val: true) -> add 4 *)
  replace 24%Z with (4 + 20)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 4: 8 (odd index: false) -> skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 5: 1 (odd index: true, even val: false) -> skip *)
  apply seao_other; [right; reflexivity |].
  (* Index 6: 8 (odd index: false) -> skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 7: 10 (odd index: true, even val: true) -> add 10 *)
  replace 20%Z with (10 + 10)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 8: 5 (odd index: false) -> skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 9: 10 (odd index: true, even val: true) -> add 10 *)
  replace 10%Z with (10 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 10: 5 (odd index: false) -> skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 11: 3 (odd index: true, even val: false) -> skip *)
  apply seao_other; [right; reflexivity |].
  (* Index 12: nil *)
  apply seao_nil.
Qed.