Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example problem_54_test_example :
  problem_54_spec "5432cababecdead" "cababecdead" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intro H. exfalso. discriminate H.
  - intro H.
    exfalso.
    specialize (H "5"%char) as [Hlr Hrl].
    assert (Hinl : In "5"%char (list_ascii_of_string "5432cababecdead")).
    { simpl. left. reflexivity. }
    specialize (Hlr Hinl) as Hinr.
    simpl in Hinr.
    destruct Hinr as [Hc|Hinr]; [discriminate Hc|].
    destruct Hinr as [Ha1|Hinr]; [discriminate Ha1|].
    destruct Hinr as [Hb1|Hinr]; [discriminate Hb1|].
    destruct Hinr as [Ha2|Hinr]; [discriminate Ha2|].
    destruct Hinr as [Hb2|Hinr]; [discriminate Hb2|].
    destruct Hinr as [He1|Hinr]; [discriminate He1|].
    destruct Hinr as [Hc2|Hinr]; [discriminate Hc2|].
    destruct Hinr as [Hd1|Hinr]; [discriminate Hd1|].
    destruct Hinr as [He2|Hinr]; [discriminate He2|].
    destruct Hinr as [Ha3|Hinr]; [discriminate Ha3|].
    destruct Hinr as [Hd2|Hinr]; [discriminate Hd2|].
    inversion Hinr.
Qed.