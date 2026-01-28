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

Example test_case : problem_85_spec [11%Z; 22%Z; 33%Z; 44%Z; 55%Z; 66%Z; 77%Z; 88%Z; 66%Z; 99%Z; 100%Z] 220%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Not odd. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 1: 22. Odd, Even. *)
  replace 220%Z with (22 + 198)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 2: 33. Not odd. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 3: 44. Odd, Even. *)
  replace 198%Z with (44 + 154)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 4: 55. Not odd. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 5: 66. Odd, Even. *)
  replace 154%Z with (66 + 88)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 6: 77. Not odd. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 7: 88. Odd, Even. *)
  replace 88%Z with (88 + 0)%Z by reflexivity.
  apply seao_odd_even; [simpl; reflexivity | simpl; reflexivity | ].
  (* Index 8: 66. Not odd. *)
  apply seao_other. left. simpl. reflexivity.
  (* Index 9: 99. Odd, but not Even. *)
  apply seao_other. right. simpl. reflexivity.
  (* Index 10: 100. Not odd. *)
  apply seao_other. left. simpl. reflexivity.
  (* Nil *)
  apply seao_nil.
Qed.