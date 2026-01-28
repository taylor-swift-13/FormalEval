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

Example test_case : problem_85_spec [11; 22; 33; 44; 55; 88; 77; 88; 99; 10; 100; 33] 252.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index, skip. *)
  apply seao_other. { left. reflexivity. }
  (* Index 1: 22. Odd index, even value. Add 22. *)
  replace 252 with (22 + 230) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 2: 33. Even index, skip. *)
  apply seao_other. { left. reflexivity. }
  (* Index 3: 44. Odd index, even value. Add 44. *)
  replace 230 with (44 + 186) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 4: 55. Even index, skip. *)
  apply seao_other. { left. reflexivity. }
  (* Index 5: 88. Odd index, even value. Add 88. *)
  replace 186 with (88 + 98) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 6: 77. Even index, skip. *)
  apply seao_other. { left. reflexivity. }
  (* Index 7: 88. Odd index, even value. Add 88. *)
  replace 98 with (88 + 10) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 8: 99. Even index, skip. *)
  apply seao_other. { left. reflexivity. }
  (* Index 9: 10. Odd index, even value. Add 10. *)
  replace 10 with (10 + 0) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 10: 100. Even index, skip. *)
  apply seao_other. { left. reflexivity. }
  (* Index 11: 33. Odd index, odd value. Skip. *)
  apply seao_other. { right. reflexivity. }
  (* Index 12: nil. *)
  apply seao_nil.
Qed.