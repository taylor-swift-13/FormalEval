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

Example test_case : problem_85_spec [1%Z; 5%Z; 3%Z; 8%Z; 1%Z; 26%Z; 10%Z; 44%Z; 9%Z; 2%Z; 44%Z] 80%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0, Val 1: Even index, skip *)
  apply seao_other.
  { left. simpl. reflexivity. }
  (* Index 1, Val 5: Odd index, Odd value, skip *)
  apply seao_other.
  { right. simpl. reflexivity. }
  (* Index 2, Val 3: Even index, skip *)
  apply seao_other.
  { left. simpl. reflexivity. }
  (* Index 3, Val 8: Odd index, Even value, add 8 *)
  replace 80 with (8 + 72) by reflexivity.
  apply seao_odd_even.
  { simpl. reflexivity. }
  { simpl. reflexivity. }
  (* Index 4, Val 1: Even index, skip *)
  apply seao_other.
  { left. simpl. reflexivity. }
  (* Index 5, Val 26: Odd index, Even value, add 26 *)
  replace 72 with (26 + 46) by reflexivity.
  apply seao_odd_even.
  { simpl. reflexivity. }
  { simpl. reflexivity. }
  (* Index 6, Val 10: Even index, skip *)
  apply seao_other.
  { left. simpl. reflexivity. }
  (* Index 7, Val 44: Odd index, Even value, add 44 *)
  replace 46 with (44 + 2) by reflexivity.
  apply seao_odd_even.
  { simpl. reflexivity. }
  { simpl. reflexivity. }
  (* Index 8, Val 9: Even index, skip *)
  apply seao_other.
  { left. simpl. reflexivity. }
  (* Index 9, Val 2: Odd index, Even value, add 2 *)
  replace 2 with (2 + 0) by reflexivity.
  apply seao_odd_even.
  { simpl. reflexivity. }
  { simpl. reflexivity. }
  (* Index 10, Val 44: Even index, skip *)
  apply seao_other.
  { left. simpl. reflexivity. }
  (* End of list *)
  apply seao_nil.
Qed.