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

Parameter v0 v2 v3 v6 v2' : Any.
Parameter four seven eight : Any.
Parameter r1 r2 r3 : Any.
Parameter n0 n2 n3 n6 : int.

Axiom isint_v0 : IsInt v0 n0.
Axiom isint_v2 : IsInt v2 n2.
Axiom isint_v3 : IsInt v3 n3.
Axiom isint_v6 : IsInt v6 n6.
Axiom isint_v2' : IsInt v2' n2.

Axiom nonint_four : forall n, ~ IsInt four n.
Axiom nonint_seven : forall n, ~ IsInt seven n.
Axiom nonint_eight : forall n, ~ IsInt eight n.
Axiom nonint_r1 : forall n, ~ IsInt r1 n.
Axiom nonint_r2 : forall n, ~ IsInt r2 n.
Axiom nonint_r3 : forall n, ~ IsInt r3 n.

Example test_case_mixed:
  filter_integers_spec
    [v0; v2; v3; four; r1; r2; v6; seven; eight; r3; v2']
    [n0; n2; n3; n6; n2].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply isint_v0|].
  eapply fir_cons_int; [apply isint_v2|].
  eapply fir_cons_int; [apply isint_v3|].
  eapply fir_cons_nonint; [exact nonint_four|].
  eapply fir_cons_nonint; [exact nonint_r1|].
  eapply fir_cons_nonint; [exact nonint_r2|].
  eapply fir_cons_int; [apply isint_v6|].
  eapply fir_cons_nonint; [exact nonint_seven|].
  eapply fir_cons_nonint; [exact nonint_eight|].
  eapply fir_cons_nonint; [exact nonint_r3|].
  eapply fir_cons_int; [apply isint_v2'|].
  apply fir_nil.
Qed.