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

Parameter v1 v2 v3 v_four v5p5 v6 v_seven v8str v9r : Any.
Parameter n1 n2 n3 n6 : int.
Axiom IsInt_v1 : IsInt v1 n1.
Axiom IsInt_v2 : IsInt v2 n2.
Axiom IsInt_v3 : IsInt v3 n3.
Axiom IsInt_v6 : IsInt v6 n6.
Axiom NonInt_v_four : forall n, ~ IsInt v_four n.
Axiom NonInt_v5p5 : forall n, ~ IsInt v5p5 n.
Axiom NonInt_v_seven : forall n, ~ IsInt v_seven n.
Axiom NonInt_v8str : forall n, ~ IsInt v8str n.
Axiom NonInt_v9r : forall n, ~ IsInt v9r n.

Example test_case_mixed: filter_integers_spec
  [v1; v2; v3; v_four; v5p5; v6; v_seven; v8str; v9r]
  [n1; n2; n3; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1|].
  eapply fir_cons_int; [apply IsInt_v2|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_nonint; [apply NonInt_v_four|].
  eapply fir_cons_nonint; [apply NonInt_v5p5|].
  eapply fir_cons_int; [apply IsInt_v6|].
  eapply fir_cons_nonint; [apply NonInt_v_seven|].
  eapply fir_cons_nonint; [apply NonInt_v8str|].
  eapply fir_cons_nonint; [apply NonInt_v9r|].
  constructor.
Qed.