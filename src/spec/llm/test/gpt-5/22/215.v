Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
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

Parameter v1 v23 v4 v5list v91 vnil v7_8 v9str vobj v1b : Any.
Parameter i1 i4 i91 i1b : int.
Axiom HIsInt_v1 : IsInt v1 i1.
Axiom HNonInt_v23 : forall n, ~ IsInt v23 n.
Axiom HIsInt_v4 : IsInt v4 i4.
Axiom HNonInt_v5list : forall n, ~ IsInt v5list n.
Axiom HIsInt_v91 : IsInt v91 i91.
Axiom HNonInt_vnil : forall n, ~ IsInt vnil n.
Axiom HNonInt_v7_8 : forall n, ~ IsInt v7_8 n.
Axiom HNonInt_v9str : forall n, ~ IsInt v9str n.
Axiom HNonInt_vobj : forall n, ~ IsInt vobj n.
Axiom HIsInt_v1b : IsInt v1b i1b.

Example test_case_new:
  filter_integers_spec
    [v1; v23; v4; v5list; v91; vnil; v7_8; v9str; vobj; v1b]
    [i1; i4; i91; i1b].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact HIsInt_v1|].
  eapply fir_cons_nonint; [apply HNonInt_v23|].
  eapply fir_cons_int; [exact HIsInt_v4|].
  eapply fir_cons_nonint; [apply HNonInt_v5list|].
  eapply fir_cons_int; [exact HIsInt_v91|].
  eapply fir_cons_nonint; [apply HNonInt_vnil|].
  eapply fir_cons_nonint; [apply HNonInt_v7_8|].
  eapply fir_cons_nonint; [apply HNonInt_v9str|].
  eapply fir_cons_nonint; [apply HNonInt_vobj|].
  eapply fir_cons_int; [exact HIsInt_v1b|].
  apply fir_nil.
Qed.