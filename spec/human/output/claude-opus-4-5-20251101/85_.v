Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Bool.Bool Coq.Arith.Arith.
Require Import Lia.
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

Example test_problem_85 : problem_85_spec [4%Z; 88%Z] 88%Z.
Proof.
  unfold problem_85_spec.
  (* Index 0: 4 is at index 0, which is even (Nat.odd 0 = false), so skip *)
  apply seao_other.
  - left. reflexivity.
  - (* Index 1: 88 is at index 1, which is odd, and 88 is even *)
    (* We need to show: sum_even_at_odd_indices_rel [88] 1 88 *)
    (* 88 = 88 + 0, so we use seao_odd_even *)
    replace 88%Z with (88 + 0)%Z by lia.
    apply seao_odd_even.
    + reflexivity.
    + reflexivity.
    + (* Empty list *)
      apply seao_nil.
Qed.