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

Example test_case : problem_85_spec [11; 22; 33; 54; 44; 55; 66; 77; 88; 66; 99; 100; 44] 242.
Proof.
  unfold problem_85_spec.
  (* i=0, h=11. odd 0 = false. *)
  apply seao_other. left. reflexivity.
  (* i=1, h=22. odd 1 = true, even 22 = true. *)
  replace 242 with (22 + 220) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=2, h=33. odd 2 = false. *)
  apply seao_other. left. reflexivity.
  (* i=3, h=54. odd 3 = true, even 54 = true. *)
  replace 220 with (54 + 166) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=4, h=44. odd 4 = false. *)
  apply seao_other. left. reflexivity.
  (* i=5, h=55. odd 5 = true, even 55 = false. *)
  apply seao_other. right. reflexivity.
  (* i=6, h=66. odd 6 = false. *)
  apply seao_other. left. reflexivity.
  (* i=7, h=77. odd 7 = true, even 77 = false. *)
  apply seao_other. right. reflexivity.
  (* i=8, h=88. odd 8 = false. *)
  apply seao_other. left. reflexivity.
  (* i=9, h=66. odd 9 = true, even 66 = true. *)
  replace 166 with (66 + 100) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=10, h=99. odd 10 = false. *)
  apply seao_other. left. reflexivity.
  (* i=11, h=100. odd 11 = true, even 100 = true. *)
  replace 100 with (100 + 0) by reflexivity.
  apply seao_odd_even. reflexivity. reflexivity.
  (* i=12, h=44. odd 12 = false. *)
  apply seao_other. left. reflexivity.
  (* nil *)
  apply seao_nil.
Qed.