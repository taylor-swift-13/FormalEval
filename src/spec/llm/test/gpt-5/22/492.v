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

Parameters v0 v2 v3 vfour vneg v55 v6 v8 v90 : Any.
Axiom IsInt_v0 : IsInt v0 0%Z.
Axiom IsInt_v2 : IsInt v2 2%Z.
Axiom IsInt_v3 : IsInt v3 3%Z.
Axiom IsInt_v6 : IsInt v6 6%Z.
Axiom NotInt_vfour : forall n, ~ IsInt vfour n.
Axiom NotInt_vneg : forall n, ~ IsInt vneg n.
Axiom NotInt_v55 : forall n, ~ IsInt v55 n.
Axiom NotInt_v8 : forall n, ~ IsInt v8 n.
Axiom NotInt_v90 : forall n, ~ IsInt v90 n.

Example test_case_new: filter_integers_spec [v0; v2; v3; vfour; vneg; v55; v6; v8; v90] [0%Z; 2%Z; 3%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0|].
  eapply fir_cons_int; [apply IsInt_v2|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_nonint; [apply NotInt_vfour|].
  eapply fir_cons_nonint; [apply NotInt_vneg|].
  eapply fir_cons_nonint; [apply NotInt_v55|].
  eapply fir_cons_int; [apply IsInt_v6|].
  eapply fir_cons_nonint; [apply NotInt_v8|].
  eapply fir_cons_nonint; [apply NotInt_v90|].
  constructor.
Qed.