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

Example test_case : problem_85_spec [11%Z; 11%Z; 22%Z; 33%Z; 66%Z; 67%Z; 77%Z; 68%Z; 88%Z; 99%Z; 101%Z] 68%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Odd index false. *)
  apply seao_other. left. reflexivity.
  (* Index 1: 11. Odd index true. Even val false. *)
  apply seao_other. right. reflexivity.
  (* Index 2: 22. Odd index false. *)
  apply seao_other. left. reflexivity.
  (* Index 3: 33. Odd index true. Even val false. *)
  apply seao_other. right. reflexivity.
  (* Index 4: 66. Odd index false. *)
  apply seao_other. left. reflexivity.
  (* Index 5: 67. Odd index true. Even val false. *)
  apply seao_other. right. reflexivity.
  (* Index 6: 77. Odd index false. *)
  apply seao_other. left. reflexivity.
  (* Index 7: 68. Odd index true. Even val true. *)
  replace 68%Z with (68 + 0)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* Index 8: 88. Odd index false. *)
  apply seao_other. left. reflexivity.
  (* Index 9: 99. Odd index true. Even val false. *)
  apply seao_other. right. reflexivity.
  (* Index 10: 101. Odd index false. *)
  apply seao_other. left. reflexivity.
  (* Nil *)
  apply seao_nil.
Qed.