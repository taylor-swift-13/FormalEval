Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

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

Parameter Vlist1 Vlist3 Vlist4 Vlist5 Vlist6 Vlist7 Vlist8 : Any.
Parameter V0 V1 : Any.

Axiom Vlist1_nonint : forall n, ~ IsInt Vlist1 n.
Axiom Vlist3_nonint : forall n, ~ IsInt Vlist3 n.
Axiom Vlist4_nonint : forall n, ~ IsInt Vlist4 n.
Axiom Vlist5_nonint : forall n, ~ IsInt Vlist5 n.
Axiom Vlist6_nonint : forall n, ~ IsInt Vlist6 n.
Axiom Vlist7_nonint : forall n, ~ IsInt Vlist7 n.
Axiom Vlist8_nonint : forall n, ~ IsInt Vlist8 n.
Axiom V0_is_int : IsInt V0 0%Z.
Axiom V1_is_int : IsInt V1 1%Z.

Example test_case_new:
  filter_integers_spec
    [Vlist1; V0; Vlist3; Vlist4; Vlist5; Vlist6; Vlist7; Vlist8; V1]
    [0%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact Vlist1_nonint|].
  eapply fir_cons_int; [exact V0_is_int|].
  eapply fir_cons_nonint; [exact Vlist3_nonint|].
  eapply fir_cons_nonint; [exact Vlist4_nonint|].
  eapply fir_cons_nonint; [exact Vlist5_nonint|].
  eapply fir_cons_nonint; [exact Vlist6_nonint|].
  eapply fir_cons_nonint; [exact Vlist7_nonint|].
  eapply fir_cons_nonint; [exact Vlist8_nonint|].
  eapply fir_cons_int; [exact V1_is_int|].
  constructor.
Qed.