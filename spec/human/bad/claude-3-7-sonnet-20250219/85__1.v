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

Example test_85 : problem_85_spec [4%Z; 88%Z] 88%Z.
Proof.
  (* Goal: sum_even_at_odd_indices_rel [4; 88] 0 88 *)
  (* Index 0 is even, 4 is even, so seao_other applies because index 0 is even. *)
  apply seao_other.
  - left. reflexivity. (* Nat.odd 0 = false *)
  - (* Need to prove sum_even_at_odd_indices_rel [88] 1 88 *)
    apply seao_odd_even.
    + reflexivity.  (* Nat.odd 1 = true *)
    + reflexivity.  (* Z.even 88 = true *)
    + apply seao_nil.
Qed.