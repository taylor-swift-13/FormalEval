Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

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

Parameter v5_8_1_6 : Any.
Parameter v2_and_string3 : Any.
Parameter v4 : Any.
Parameter v5_8_1_6_bis : Any.
Parameter v7_8 : Any.
Parameter v4_bis : Any.
Parameter a0 : Any.
Parameter a1 : Any.

Axiom nonint_v5_8_1_6 : forall n, ~ IsInt v5_8_1_6 n.
Axiom nonint_v2_and_string3 : forall n, ~ IsInt v2_and_string3 n.
Axiom nonint_v4 : forall n, ~ IsInt v4 n.
Axiom nonint_v5_8_1_6_bis : forall n, ~ IsInt v5_8_1_6_bis n.
Axiom nonint_v7_8 : forall n, ~ IsInt v7_8 n.
Axiom nonint_v4_bis : forall n, ~ IsInt v4_bis n.

Axiom a0_is_int : IsInt a0 0%Z.
Axiom a1_is_int : IsInt a1 1%Z.

Example test_case_filter_integers: filter_integers_spec [v5_8_1_6; a0; v2_and_string3; v4; v5_8_1_6_bis; v7_8; a1; v4_bis] [0%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [intros n; apply nonint_v5_8_1_6|].
  eapply fir_cons_int; [apply a0_is_int|].
  eapply fir_cons_nonint; [intros n; apply nonint_v2_and_string3|].
  eapply fir_cons_nonint; [intros n; apply nonint_v4|].
  eapply fir_cons_nonint; [intros n; apply nonint_v5_8_1_6_bis|].
  eapply fir_cons_nonint; [intros n; apply nonint_v7_8|].
  eapply fir_cons_int; [apply a1_is_int|].
  eapply fir_cons_nonint; [intros n; apply nonint_v4_bis|].
  apply fir_nil.
Qed.