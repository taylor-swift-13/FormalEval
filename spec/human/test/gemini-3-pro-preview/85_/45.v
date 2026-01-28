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

Example test_case : problem_85_spec [1%Z; 2%Z; 3%Z; 4%Z; 3%Z; 2%Z; 1%Z; 3%Z; 1%Z] 8%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 1. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 1: 2. Odd index, even value. 8 = 2 + 6. *)
  replace 8 with (2 + 6) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 2: 3. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 3: 4. Odd index, even value. 6 = 4 + 2. *)
  replace 6 with (4 + 2) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 4: 3. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 5: 2. Odd index, even value. 2 = 2 + 0. *)
  replace 2 with (2 + 0) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 6: 1. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 7: 3. Odd index, odd value. *)
  apply seao_other. { right. reflexivity. }
  (* Index 8: 1. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* End of list *)
  apply seao_nil.
Qed.