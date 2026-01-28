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

Example test_case : problem_85_spec [2%Z; 4%Z; 6%Z; 17%Z; 10%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z; 17%Z; 24%Z; 13%Z; 28%Z; 30%Z; 6%Z; 4%Z; 2%Z; 4%Z; 18%Z; 18%Z] 138%Z.
Proof.
  unfold problem_85_spec.
  repeat (
    apply seao_nil ||
    (apply seao_other; [ left; reflexivity | ]) ||
    (apply seao_other; [ right; reflexivity | ]) ||
    match goal with
    | [ |- sum_even_at_odd_indices_rel (?h :: _) _ ?s ] =>
        replace s with (h + (s - h))%Z by (vm_compute; reflexivity);
        apply seao_odd_even; [ reflexivity | reflexivity | ]
    end
  ).
Qed.