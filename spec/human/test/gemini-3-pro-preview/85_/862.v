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

Example test_case : problem_85_spec [21%Z; 22%Z; 33%Z; 55%Z; 65%Z; 88%Z; 99%Z; 99%Z; 11%Z] 110%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 21. Nat.odd 0 = false. *)
  apply seao_other. { left. reflexivity. }
  (* Index 1: 22. Nat.odd 1 = true, Z.even 22 = true. Sum += 22. *)
  replace 110%Z with (22 + 88)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 2: 33. Nat.odd 2 = false. *)
  apply seao_other. { left. reflexivity. }
  (* Index 3: 55. Nat.odd 3 = true, Z.even 55 = false. *)
  apply seao_other. { right. reflexivity. }
  (* Index 4: 65. Nat.odd 4 = false. *)
  apply seao_other. { left. reflexivity. }
  (* Index 5: 88. Nat.odd 5 = true, Z.even 88 = true. Sum += 88. *)
  replace 88%Z with (88 + 0)%Z by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 6: 99. Nat.odd 6 = false. *)
  apply seao_other. { left. reflexivity. }
  (* Index 7: 99. Nat.odd 7 = true, Z.even 99 = false. *)
  apply seao_other. { right. reflexivity. }
  (* Index 8: 11. Nat.odd 8 = false. *)
  apply seao_other. { left. reflexivity. }
  (* Nil *)
  apply seao_nil.
Qed.