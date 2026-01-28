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

Example test_case : problem_85_spec [3%Z; 22%Z; 1%Z; 6%Z; 7%Z; 8%Z; 1%Z; 9%Z; 9%Z; 6%Z; 23%Z; 8%Z; 1%Z] 50%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 3 (odd index false) *)
  apply seao_other. left; reflexivity.
  (* Index 1: 22 (odd index true, even val true) -> sum += 22 *)
  replace 50%Z with (22 + 28)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 2: 1 (odd index false) *)
  apply seao_other. left; reflexivity.
  (* Index 3: 6 (odd index true, even val true) -> sum += 6 *)
  replace 28%Z with (6 + 22)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 4: 7 (odd index false) *)
  apply seao_other. left; reflexivity.
  (* Index 5: 8 (odd index true, even val true) -> sum += 8 *)
  replace 22%Z with (8 + 14)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 6: 1 (odd index false) *)
  apply seao_other. left; reflexivity.
  (* Index 7: 9 (odd index true, even val false) *)
  apply seao_other. right; reflexivity.
  (* Index 8: 9 (odd index false) *)
  apply seao_other. left; reflexivity.
  (* Index 9: 6 (odd index true, even val true) -> sum += 6 *)
  replace 14%Z with (6 + 8)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 10: 23 (odd index false) *)
  apply seao_other. left; reflexivity.
  (* Index 11: 8 (odd index true, even val true) -> sum += 8 *)
  replace 8%Z with (8 + 0)%Z by reflexivity.
  apply seao_odd_even; [reflexivity | reflexivity | ].
  (* Index 12: 1 (odd index false) *)
  apply seao_other. left; reflexivity.
  (* End of list *)
  apply seao_nil.
Qed.