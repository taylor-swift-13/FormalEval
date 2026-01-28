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

Example test_case : problem_85_spec [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 6; 42; 13; 14; 15; 17; 18; 19; 10]%Z 54%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. { left. simpl. reflexivity. }
  replace 54 with (2 + 52) by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  replace 52 with (4 + 48) by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  replace 48 with (6 + 42) by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  replace 42 with (8 + 34) by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  apply seao_other. { right. simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  replace 34 with (6 + 28) by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  apply seao_other. { right. simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  apply seao_other. { right. simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  replace 28 with (18 + 10) by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  apply seao_other. { left. simpl. reflexivity. }
  replace 10 with (10 + 0) by reflexivity.
  apply seao_odd_even. { simpl. reflexivity. } { simpl. reflexivity. }
  apply seao_nil.
Qed.