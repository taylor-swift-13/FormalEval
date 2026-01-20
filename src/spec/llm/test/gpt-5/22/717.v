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

Parameter v0 v2 vstr3 v4 v56R vListR vDict1 vEmptyDict vTrue vDict2 vFalse : Any.
Axiom IsInt_v0 : IsInt v0 0%Z.
Axiom IsInt_v2 : IsInt v2 2%Z.
Axiom IsInt_v4 : IsInt v4 4%Z.
Axiom NotInt_vstr3 : forall n, ~ IsInt vstr3 n.
Axiom NotInt_v56R : forall n, ~ IsInt v56R n.
Axiom NotInt_vListR : forall n, ~ IsInt vListR n.
Axiom NotInt_vDict1 : forall n, ~ IsInt vDict1 n.
Axiom NotInt_vEmptyDict : forall n, ~ IsInt vEmptyDict n.
Axiom NotInt_vTrue : forall n, ~ IsInt vTrue n.
Axiom NotInt_vDict2 : forall n, ~ IsInt vDict2 n.
Axiom NotInt_vFalse : forall n, ~ IsInt vFalse n.

Example test_case_nonempty: filter_integers_spec [v0; v2; vstr3; v4; v56R; vListR; vDict1; vEmptyDict; vTrue; vDict2; vFalse] [0%Z; 2%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0 |].
  eapply fir_cons_int; [apply IsInt_v2 |].
  eapply fir_cons_nonint; [apply NotInt_vstr3 |].
  eapply fir_cons_int; [apply IsInt_v4 |].
  eapply fir_cons_nonint; [apply NotInt_v56R |].
  eapply fir_cons_nonint; [apply NotInt_vListR |].
  eapply fir_cons_nonint; [apply NotInt_vDict1 |].
  eapply fir_cons_nonint; [apply NotInt_vEmptyDict |].
  eapply fir_cons_nonint; [apply NotInt_vTrue |].
  eapply fir_cons_nonint; [apply NotInt_vDict2 |].
  eapply fir_cons_nonint; [apply NotInt_vFalse |].
  apply fir_nil.
Qed.