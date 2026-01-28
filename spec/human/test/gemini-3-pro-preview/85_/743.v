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

Example test_case : problem_85_spec [1; 2; 3; 4; 5; 42; 7; 7; 9; 10; 11; 12; 13; 14; 67; 15; 16; 17; 18; 19; 20; 1; 10]%Z 84%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. { left. reflexivity. }
  replace 84 with (2 + 82) by reflexivity. apply seao_odd_even. { reflexivity. } { reflexivity. }
  apply seao_other. { left. reflexivity. }
  replace 82 with (4 + 78) by reflexivity. apply seao_odd_even. { reflexivity. } { reflexivity. }
  apply seao_other. { left. reflexivity. }
  replace 78 with (42 + 36) by reflexivity. apply seao_odd_even. { reflexivity. } { reflexivity. }
  apply seao_other. { left. reflexivity. }
  apply seao_other. { right. reflexivity. }
  apply seao_other. { left. reflexivity. }
  replace 36 with (10 + 26) by reflexivity. apply seao_odd_even. { reflexivity. } { reflexivity. }
  apply seao_other. { left. reflexivity. }
  replace 26 with (12 + 14) by reflexivity. apply seao_odd_even. { reflexivity. } { reflexivity. }
  apply seao_other. { left. reflexivity. }
  replace 14 with (14 + 0) by reflexivity. apply seao_odd_even. { reflexivity. } { reflexivity. }
  apply seao_other. { left. reflexivity. }
  apply seao_other. { right. reflexivity. }
  apply seao_other. { left. reflexivity. }
  apply seao_other. { right. reflexivity. }
  apply seao_other. { left. reflexivity. }
  apply seao_other. { right. reflexivity. }
  apply seao_other. { left. reflexivity. }
  apply seao_other. { right. reflexivity. }
  apply seao_other. { left. reflexivity. }
  apply seao_nil.
Qed.