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

Example test_case : problem_85_spec [11; 8; 30; 66; 67; 77; 88; 77; 99; 100; 77; 76; 100; 66; 66]%Z 316%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 11. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 1: 8. Odd index, Even value. 316 = 8 + 308. *)
  replace 316 with (8 + 308) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 2: 30. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 3: 66. Odd index, Even value. 308 = 66 + 242. *)
  replace 308 with (66 + 242) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 4: 67. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 5: 77. Odd index, Odd value. *)
  apply seao_other. { right. reflexivity. }
  (* Index 6: 88. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 7: 77. Odd index, Odd value. *)
  apply seao_other. { right. reflexivity. }
  (* Index 8: 99. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 9: 100. Odd index, Even value. 242 = 100 + 142. *)
  replace 242 with (100 + 142) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 10: 77. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 11: 76. Odd index, Even value. 142 = 76 + 66. *)
  replace 142 with (76 + 66) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 12: 100. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Index 13: 66. Odd index, Even value. 66 = 66 + 0. *)
  replace 66 with (66 + 0) by reflexivity.
  apply seao_odd_even. { reflexivity. } { reflexivity. }
  (* Index 14: 66. Even index. *)
  apply seao_other. { left. reflexivity. }
  (* Nil *)
  apply seao_nil.
Qed.