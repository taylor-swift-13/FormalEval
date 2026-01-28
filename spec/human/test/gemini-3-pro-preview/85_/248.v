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

Example test_case : problem_85_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z; 8%Z; 9%Z; 11%Z; 12%Z; 42%Z; 13%Z; 14%Z; 15%Z; 19%Z; 18%Z; 19%Z; 10%Z; 4%Z] 80%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 1: 2 - odd index, even value, add 2 *)
  replace 80%Z with (2 + 78)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 2: 3 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 3: 4 - odd index, even value, add 4 *)
  replace 78%Z with (4 + 74)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 4: 5 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 5: 6 - odd index, even value, add 6 *)
  replace 74%Z with (6 + 68)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 6: 7 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 7: 8 - odd index, even value, add 8 *)
  replace 68%Z with (8 + 60)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 8: 9 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 9: 11 - odd index, odd value, skip *)
  apply seao_other; [right; reflexivity |].
  (* Index 10: 12 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 11: 42 - odd index, even value, add 42 *)
  replace 60%Z with (42 + 18)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 12: 13 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 13: 14 - odd index, even value, add 14 *)
  replace 18%Z with (14 + 4)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Index 14: 15 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 15: 19 - odd index, odd value, skip *)
  apply seao_other; [right; reflexivity |].
  (* Index 16: 18 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 17: 19 - odd index, odd value, skip *)
  apply seao_other; [right; reflexivity |].
  (* Index 18: 10 - even index, skip *)
  apply seao_other; [left; reflexivity |].
  (* Index 19: 4 - odd index, even value, add 4 *)
  replace 4%Z with (4 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity |].
  (* Nil *)
  apply seao_nil.
Qed.