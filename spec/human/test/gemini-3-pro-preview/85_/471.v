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

Example test_case : problem_85_spec [2; 4; 6; 8; 10; 14; 16; 18; 20; 22; 24; 26; 28; 30; 28; 14; 4]%Z 136%Z.
Proof.
  unfold problem_85_spec.
  apply seao_other. left; reflexivity.
  replace 136%Z with (4 + 132)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 132%Z with (8 + 124)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 124%Z with (14 + 110)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 110%Z with (18 + 92)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 92%Z with (22 + 70)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 70%Z with (26 + 44)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 44%Z with (30 + 14)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  replace 14%Z with (14 + 0)%Z by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  apply seao_other. left; reflexivity.
  apply seao_nil.
Qed.