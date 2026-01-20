Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Parameters a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : Any.
Hypothesis hi1 : IsInt a1 10%Z.
Hypothesis hn2 : forall n, ~ IsInt a2 n.
Hypothesis hn3 : forall n, ~ IsInt a3 n.
Hypothesis hi4 : IsInt a4 8%Z.
Hypothesis hn5 : forall n, ~ IsInt a5 n.
Hypothesis hn6 : forall n, ~ IsInt a6 n.
Hypothesis hi7 : IsInt a7 9%Z.
Hypothesis hi8 : IsInt a8 9%Z.
Hypothesis hi9 : IsInt a9 6%Z.
Hypothesis hn10 : forall n, ~ IsInt a10 n.
Hypothesis hn11 : forall n, ~ IsInt a11 n.
Hypothesis hi12 : IsInt a12 9%Z.
Hypothesis hn13 : forall n, ~ IsInt a13 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11; a12; a13] [10%Z; 8%Z; 9%Z; 9%Z; 6%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact hi1|].
  eapply fir_cons_nonint; [exact hn2|].
  eapply fir_cons_nonint; [exact hn3|].
  eapply fir_cons_int; [exact hi4|].
  eapply fir_cons_nonint; [exact hn5|].
  eapply fir_cons_nonint; [exact hn6|].
  eapply fir_cons_int; [exact hi7|].
  eapply fir_cons_int; [exact hi8|].
  eapply fir_cons_int; [exact hi9|].
  eapply fir_cons_nonint; [exact hn10|].
  eapply fir_cons_nonint; [exact hn11|].
  eapply fir_cons_int; [exact hi12|].
  eapply fir_cons_nonint; [exact hn13|].
  constructor.
Qed.