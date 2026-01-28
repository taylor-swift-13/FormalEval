Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_odd_in_even_pos_rel : list Z -> Z -> Z -> Prop :=
| soep_nil : forall i, sum_odd_in_even_pos_rel [] i 0
| soep_match : forall h t i s_tail, Z.even i = true -> Z.even h = false ->
    sum_odd_in_even_pos_rel t (i + 1) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i (h + s_tail)
| soep_skip : forall h t i s_tail, (Z.even i = false \/ Z.even h = true) ->
    sum_odd_in_even_pos_rel t (i + 1) s_tail ->
    sum_odd_in_even_pos_rel (h :: t) i s_tail.

Definition problem_121_pre (l : list Z) : Prop := l <> [].

Definition problem_121_spec (l : list Z) (output : Z) : Prop :=
  sum_odd_in_even_pos_rel l 0 output.

Example test_case : problem_121_spec [1; 1; 2; 1; -1; 1; 1; 1; 1; 1; 1; 1] 3.
Proof.
  unfold problem_121_spec.
  apply soep_match with (s_tail := 2); [reflexivity | reflexivity | ].
  apply soep_skip; [left; reflexivity | ].
  apply soep_skip; [right; reflexivity | ].
  apply soep_skip; [left; reflexivity | ].
  apply soep_match with (s_tail := 3); [reflexivity | reflexivity | ].
  apply soep_skip; [left; reflexivity | ].
  apply soep_match with (s_tail := 2); [reflexivity | reflexivity | ].
  apply soep_skip; [left; reflexivity | ].
  apply soep_match with (s_tail := 1); [reflexivity | reflexivity | ].
  apply soep_skip; [left; reflexivity | ].
  apply soep_match with (s_tail := 0); [reflexivity | reflexivity | ].
  apply soep_skip; [left; reflexivity | ].
  apply soep_nil.
Qed.