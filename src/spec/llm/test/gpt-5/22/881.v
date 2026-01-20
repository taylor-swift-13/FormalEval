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

Parameter a_list3 a1 a_str a_list55_1 a_list55_2 a7 a_list55_3 : Any.
Axiom H_a1 : IsInt a1 1%Z.
Axiom H_a7 : IsInt a7 7%Z.
Axiom H_nint_list3 : forall n, ~ IsInt a_list3 n.
Axiom H_nint_str : forall n, ~ IsInt a_str n.
Axiom H_nint_list55_1 : forall n, ~ IsInt a_list55_1 n.
Axiom H_nint_list55_2 : forall n, ~ IsInt a_list55_2 n.
Axiom H_nint_list55_3 : forall n, ~ IsInt a_list55_3 n.

Example test_case_new:
  filter_integers_spec
    [a_list3; a1; a_str; a_list55_1; a_list55_2; a7; a_list55_3]
    [1%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. apply H_nint_list3.
  eapply fir_cons_int. apply H_a1.
  eapply fir_cons_nonint. apply H_nint_str.
  eapply fir_cons_nonint. apply H_nint_list55_1.
  eapply fir_cons_nonint. apply H_nint_list55_2.
  eapply fir_cons_int. apply H_a7.
  eapply fir_cons_nonint. apply H_nint_list55_3.
  constructor.
Qed.