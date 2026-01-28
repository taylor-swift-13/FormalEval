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

Example test_case : problem_85_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 6%Z; 3%Z; 8%Z; 10%Z; 556%Z; 100%Z; 187%Z; 42%Z; 37%Z; 29%Z; 44%Z; 8%Z; 187%Z] 614%Z.
Proof.
  unfold problem_85_spec.
  Ltac solve_step :=
    match goal with
    | [ |- sum_even_at_odd_indices_rel [] _ _ ] => apply seao_nil
    | [ |- sum_even_at_odd_indices_rel (?h :: ?t) ?i ?s ] =>
        let is_odd := eval compute in (Nat.odd i) in
        match is_odd with
        | true =>
            let is_even_val := eval compute in (Z.even h) in
            match is_even_val with
            | true =>
                let rem := eval compute in (s - h) in
                replace s with (h + rem)%Z by reflexivity;
                apply seao_odd_even; [ reflexivity | reflexivity | ]
            | false =>
                apply seao_other; [ right; reflexivity | ]
            end
        | false =>
            apply seao_other; [ left; reflexivity | ]
        end
    end.
  repeat solve_step.
Qed.