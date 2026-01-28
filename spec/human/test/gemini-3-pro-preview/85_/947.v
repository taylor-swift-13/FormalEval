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

Example test_case : problem_85_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 42%Z; 7%Z; 7%Z; 556%Z; 42%Z; 10%Z; 11%Z; 12%Z; 13%Z; 14%Z; 15%Z; 16%Z; 17%Z; 31%Z; 19%Z; 20%Z; 42%Z] 132%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 1: 2 *)
  replace 132%Z with (2 + 130)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 2: 3 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 3: 4 *)
  replace 130%Z with (4 + 126)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 4: 5 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 5: 42 *)
  replace 126%Z with (42 + 84)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 7 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 7: 7 *)
  apply seao_other; [right; reflexivity | ].
  (* Index 8: 556 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 9: 42 *)
  replace 84%Z with (42 + 42)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 10: 10 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 11: 11 *)
  apply seao_other; [right; reflexivity | ].
  (* Index 12: 12 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 13: 13 *)
  apply seao_other; [right; reflexivity | ].
  (* Index 14: 14 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 15: 15 *)
  apply seao_other; [right; reflexivity | ].
  (* Index 16: 16 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 17: 17 *)
  apply seao_other; [right; reflexivity | ].
  (* Index 18: 31 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 19: 19 *)
  apply seao_other; [right; reflexivity | ].
  (* Index 20: 20 *)
  apply seao_other; [left; reflexivity | ].
  (* Index 21: 42 *)
  replace 42%Z with (42 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Nil *)
  apply seao_nil.
Qed.